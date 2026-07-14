# MORKL trie vs reference benchmarks

`eval` = reference Set[List[PathItem]] evaluator; `evalT` = TreeMap[PathItem] trie; `evalI` = interned IntMap trie (PathItems interned to Ints before evaluation).
evalI/eval and evalI/evalT are speedups (higher = evalI faster).

## Benchmark run (2026-06-24)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       5.8 |       2.6 |       2.1 |     2.7x |    1.2x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      15.1 |       6.5 |       4.1 |     3.7x |    1.6x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     172.5 |      15.1 |       6.9 |    25.1x |    2.2x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2522.8 |     103.6 |      43.6 |    57.9x |    2.4x |  |
| aunt-query       | family n=150         |      11.4 |       1.2 |       0.7 |    16.2x |    1.7x |  |
| aunt-query       | family n=400         |      83.9 |       5.7 |       2.4 |    35.0x |    2.4x |  |
| aunt-query       | family n=800         |     352.8 |      19.9 |       8.9 |    39.6x |    2.2x |  |
| aunt-query       | family n=1600        |    1645.9 |      78.2 |      33.3 |    49.5x |    2.3x |  |
| game-of-life     | 16x16 2 steps (68 live) |      16.8 |      14.8 |       9.9 |     1.7x |    1.5x |  |
| game-of-life     | 24x24 2 steps (193 live) |      52.1 |      23.3 |      18.1 |     2.9x |    1.3x |  |
| game-of-life     | 32x32 2 steps (321 live) |     119.2 |      27.5 |      16.3 |     7.3x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.8 |       0.0 |       0.0 |   131.9x |    1.2x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |    73.7x |    1.4x |  |
| temperature      | 16384 cells (resident) |       1.3 |       0.0 |       0.0 |   951.9x |    1.8x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      70.1 |      15.9 |      13.9 |     5.1x |    1.1x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     118.2 |      37.0 |      29.2 |     4.1x |    1.3x |  |
| n-queens         | n=6 (4 sols, pure)   |      24.7 |       4.6 |       4.2 |     5.9x |    1.1x |  |
| n-queens         | n=7 (40 sols, pure)  |     127.6 |      13.2 |       9.0 |    14.2x |    1.5x |  |
| n-queens         | n=8 (92 sols, pure)  |     736.2 |      58.6 |      39.2 |    18.8x |    1.5x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     0.9x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.1 |      -1.0 |       0.1 |     0.9x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.6 |      -1.0 |       0.2 |     3.5x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       2.6 |      -1.0 |       0.2 |    16.3x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 16.7x vs the
reference Set, and 1.6x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Analysis — interned IntMap trie (evalI)

Every `PathItem` is interned to an `Int` once via a global, O(1) `Interner` (a ConcurrentHashMap
+ an array); the trie's children are then `IntMap[ITrie]` (a big-endian Patricia trie).  Two
things follow:

- **Evaluation touches no `PathItem`s.**  Path constants are interned at singleton/wrap
  construction; the ring/prefix/tails operations only combine interned ints.  Un-interning
  happens solely at the `toSpaceValue` boundary (and grounded host functions re-intern their
  outputs there).
- **The ring ops are IntMap merges.**  `union` = `IntMap.unionWith(recursive union)`,
  `intersection` = `IntMap.intersectionWith(recursive intersection)` — the callback forms line
  up exactly with the algebra and merge two child maps in one O(n+m) structural pass instead of
  per-key `TreeMap` updates.

Result vs the reference Set and vs the TreeMap trie (`evalT`):

- vs **reference**: datalog 4.4x → 31.8x (n=128: 1.3 s → 42 ms), aunt up to 41.7x (1600
  people), temperature 64–944x, Game of Life up to 7.7x, sliding 4.0–4.7x, n-queens up to
  18.2x.  Geometric mean ≈ **16x** across the six example domains.
- vs **TreeMap trie**: a consistent **1.1–2.4x** on top (geomean ≈ 1.5x), from int-keyed IntMap
  merges + no per-node `PathItem` comparisons/allocation.
- **meet-all** 3.5x → 16.3x over pairwise reduce on the interned trie (the n-ary asymptotic);
  **join-all** ~parity at these sizes.

Interning is global because it is constant time and ids are stable for the process; the same
symbol always maps to the same int, so `ITrie == ITrie` remains exact set-equality.

## Loop-invariant subgraph hoisting — A/B (2026-06-25)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth (hoisting an invariant inner
loop to the root lowers it; n-queens has no invariant inner loop, so it is unchanged).

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      1.31 |      0.77 |    1.7x |     2 |     1 |
| invariant-inner N=400  |      2.16 |      0.64 |    3.4x |     2 |     1 |
| sliding expandStep 3x3 |      1.09 |      0.27 |    4.1x |    17 |    17 |
| n-queens place(6)      |      3.22 |      3.01 |    1.1x |     7 |     7 |


## Performance campaign — interned-trie + op-graph speedups (2026-06-25)

A single coherent strategy — **carry `Space.Literal` payloads by reference** and make the **interned
`ITrie` ring operations IntMap-native** — cut the steady-state **comp+run geometric mean ≈4.4×**
(best uncontended runs reach 5×) across the ten op-graph benchmarks, with **zero test regressions**
(157/0/4) verified by the 300-program + 60-fixpoint property suite plus the full example suite.

**The two changes (each toggled by `-Dmorkl.literalByRef`/`-Dmorkl.patriciaOps`, default on):**

1. **Literals by reference** (`LiteralStore`).  `transpile` used to base64-serialize a `Space.Literal`
   into the node's `constant` string, and the CSE pass then re-hashed that multi-MB string every
   round — the 16384-cell temperature grid took ~226 ms *just to transpile*.  Now the live
   `SpaceValue` is interned to a stable, value-keyed id (`lit#N`): O(1) transpile, O(1) CSE hashing,
   and value-equal literals still share an id so structural sharing/CSE are unaffected.  The lossless
   `LiteralCodec` text form is still produced on demand (untranspile/serialization).

2. **IntMap-native ring ops** (`IntTrieOps`, in `package scala.collection.immutable` so it can see
   IntMap's Patricia structure `Bin/Tip/Nil` + `IntMapUtils.bin/join`).  union / intersection /
   difference / **restriction** become single simultaneous descents over both tries — no per-key
   `get`+`updated`, whole shared sub-tries skipped by pointer identity — and `tailsUnion`'s n-ary
   `joinAll` is a balanced pairwise merge instead of a boxed-`Int` HashMap regroup.  Plus an
   early-exit `sizeAtMost` for the `Range` cardinality window and stack-frame reuse in the executor's
   iteration/fixpoint loops.

**Per-change attribution (ablation, 10-benchmark geomean, ms, steady-state warm, best of 3 trials):**

| config | comp+run geomean | vs baseline | run-only geomean | vs baseline |
|---|---:|---:|---:|---:|
| baseline (both off)      | 4.26 | 1.0× | 0.335 | 1.0× |
| + literals-by-ref only   | 1.71 | 2.5× | 0.38  | ~1×  |
| + IntMap-native ops only | 4.21 | 1.0× | 0.234 | 1.4× |
| **both (optimized)**     | **0.96–1.11** | **~4.4× (best 5×)** | **0.11–0.14** | **~3×** |

Literals-by-ref is a pure **compile** win (it does not touch run time); the IntMap-native ops are a
pure **run** win — restriction and `joinAll` were the real hot ops (datalog's `edges <| nbs` and `⋁`,
aunt/sliding's restriction).  They are orthogonal and compose to the full speedup.

**Remaining (non-low-hanging) ceiling:** n-queens *compile* is genuine push_out LICM work over the
large inlined `place(n,n)` graph (placement is memoized, `allRefs` is linear-in-depth — no asymptotic
bug); datalog's `next(m)=m∪step(m)` Fixpoint is cumulative **and bilinear** (m joined with m), so a
correct semi-naive needs the non-linear product rule and a soundness check — deferred as higher-risk.

## Optimization across all SC domains (2026-06-25)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.31 |      0.27 |      0.16 |    1.6x |      0.14 |   0.9x |
| aunt (royal92)     |     4.62 |      5.85 |      4.39 |    1.3x |      2.45 |   0.6x |
| n-queens n=7       |    15.48 |      6.44 |      3.85 |    1.7x |      3.83 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    1.1x |      0.00 |   1.0x |
| datalog tc (n=80)  |     3.41 |      3.34 |      3.49 |    1.0x |      3.33 |   1.0x |
| sliding 3x3 step   |     1.48 |      0.22 |      0.05 |    4.1x |      0.17 |   3.1x |
| gol step 12x12     |     2.80 |      1.61 |      1.03 |    1.6x |      1.04 |   1.0x |

## Op-graph backend benchmark (2026-06-25)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.6 |     10.9 |      1.3 |       0.3 |           0.3 |     0.49 |
| aunt n=400           |      0.4 |     71.1 |      2.4 |       1.4 |           1.5 |     3.32 |
| n-queens n=6         |      2.2 |     27.1 |      4.4 |       4.3 |           1.0 |     0.44 |
| n-queens n=7         |      5.8 |    106.3 |      9.7 |       9.6 |           3.1 |     0.53 |
| temperature 4096     |      0.0 |      2.8 |      0.0 |       0.0 |           0.0 |     1.39 |
| temperature 16384    |      0.0 |      1.2 |      0.0 |       0.0 |           0.0 |     5.00 |
| gol step 12x12       |      2.2 |     11.4 |      2.1 |       1.0 |           0.6 |     0.26 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.86 ms ONCE, run = 0.583 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.583 ms (vs the compiled-in literal, recompiled per grid: 1.44 ms each).

| union_iter           |      0.0 |      0.5 |      0.0 |       0.0 |           0.0 |     0.39 |
| datalog tc n=40        |      1.3 |        — |      0.8 |       0.8 |           0.8 |     0.60 |
| datalog tc n=80        |      5.6 |        — |      3.7 |       3.7 |           3.7 |     0.67 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.19 |     0.86 |       8 |      0.24 |       4 |     1.69 |      1.98 |
| aunt n=400           |      0.11 |     0.61 |       8 |      0.19 |       4 |     0.94 |      2.40 |
| n-queens n=6         |      0.71 |     2.59 |     184 |      1.24 |     200 |     4.81 |      5.79 |
| n-queens n=7         |      1.26 |     1.79 |     215 |      0.82 |     234 |     3.98 |      7.05 |
| temperature 4096     |      0.04 |     0.04 |       0 |      0.02 |       1 |     0.10 |      0.11 |
| temperature 16384    |      0.10 |     0.03 |       0 |      0.01 |       1 |     0.15 |      0.15 |
| gol step 12x12       |      0.05 |     0.49 |      60 |      0.24 |      97 |     0.90 |      1.48 |
| union_iter           |      0.01 |     0.06 |       2 |      0.03 |       0 |     0.10 |      0.11 |
| datalog tc n=40        |      0.02 |     0.03 |       0 |      0.01 |       0 |     0.06 |      0.82 |
| datalog tc n=80        |      0.02 |     0.02 |       0 |      0.01 |       0 |     0.05 |      3.78 |

**comp+run geomean = 1.046 ms ; run-only geomean = 0.197 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).


## Pipeline-stage ablation (2026-06-25)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    1.176 |    0.647 |    0.520 |    1.980 |    1.301 |
| datalog tc (n=15)  |    2.788 |    0.945 |    0.072 |    1.271 |    0.173 |
| gol step (glider)  |    2.011 |    1.285 |    0.534 |    2.751 |    1.899 |
| sliding 3x3 step   |   10.168 |    6.680 |    0.175 |   11.289 |    2.800 |
| n-queens n=6       |   28.623 |    9.355 |    2.758 |    5.840 |    9.693 |
| temperature 1024   |    0.257 |    0.093 |    0.082 |    0.196 |    0.117 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.15 |      0.06 |    2.4x |     2 |     1 |
| invariant-inner N=400  |      0.39 |      0.17 |    2.4x |     2 |     1 |
| sliding expandStep 3x3 |      0.62 |      0.19 |    3.3x |    17 |    17 |
| n-queens place(6)      |      2.88 |      2.85 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       2.6 |       0.5 |       0.3 |     8.2x |    1.4x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.8 |       2.4 |       0.8 |    16.2x |    3.0x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     152.3 |      15.3 |       2.2 |    68.5x |    6.9x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2117.5 |     103.4 |      13.2 |   160.6x |    7.8x |  |
| aunt-query       | family n=150         |      13.4 |       0.9 |       0.2 |    71.0x |    4.7x |  |
| aunt-query       | family n=400         |      90.2 |       5.4 |       0.3 |   261.4x |   15.5x |  |
| aunt-query       | family n=800         |     381.3 |      20.1 |       0.6 |   686.3x |   36.1x |  |
| aunt-query       | family n=1600        |    1710.4 |      80.9 |       1.1 |  1529.6x |   72.4x |  |
| game-of-life     | 16x16 2 steps (68 live) |      27.6 |       7.6 |       6.3 |     4.4x |    1.2x |  |
| game-of-life     | 24x24 2 steps (193 live) |     103.2 |      14.1 |       9.2 |    11.2x |    1.5x |  |
| game-of-life     | 32x32 2 steps (321 live) |     270.2 |      25.2 |      15.2 |    17.7x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   409.1x |    3.4x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1650.8x |    3.3x |  |
| temperature      | 16384 cells (resident) |       1.5 |       0.0 |       0.0 |  5106.3x |    4.1x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      22.0 |       9.7 |       6.4 |     3.4x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     109.2 |      36.3 |      24.6 |     4.4x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      23.8 |       3.5 |       1.9 |    12.4x |    1.8x |  |
| n-queens         | n=7 (40 sols, pure)  |     122.0 |      12.4 |       6.0 |    20.3x |    2.1x |  |
| n-queens         | n=8 (92 sols, pure)  |     696.2 |      55.9 |      26.5 |    26.3x |    2.1x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     0.9x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.2 |     0.0x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.6 |     0.0x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 61.1x vs the
reference Set, and 3.8x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     12.2 |      0.1 |       0.1 |           0.1 |     0.81 |
| aunt n=400           |      0.2 |     80.0 |      0.3 |       0.2 |           0.2 |     0.82 |
| n-queens n=6         |      1.5 |     23.9 |      3.6 |       3.6 |           0.8 |     0.53 |
| n-queens n=7         |      6.5 |    113.0 |     11.2 |      11.2 |           3.2 |     0.50 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.61 |
| temperature 16384    |      0.0 |      1.7 |      0.0 |       0.0 |           0.0 |     2.00 |
| gol step 12x12       |      1.3 |     18.5 |      1.5 |       1.5 |           0.6 |     0.42 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.52 ms ONCE, run = 0.552 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.552 ms (vs the compiled-in literal, recompiled per grid: 1.07 ms each).

| union_iter           |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     0.65 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.68 |
| datalog tc n=80        |      6.9 |        — |      4.6 |       4.6 |           4.6 |     0.67 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.30 |      0.37 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.12 |     0.42 |     184 |      0.16 |     200 |     0.77 |      1.54 |
| n-queens n=7         |      0.11 |     0.52 |     215 |      0.21 |     234 |     0.90 |      4.14 |
| temperature 4096     |      0.07 |     0.01 |       0 |      0.00 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.23 |     0.01 |       0 |      0.00 |       1 |     0.26 |      0.26 |
| gol step 12x12       |      0.14 |     0.35 |     102 |      0.12 |     221 |     0.67 |      1.23 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.24 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      4.65 |

**comp+run geomean = 0.489 ms ; run-only geomean = 0.104 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.4x |      0.00 |   1.0x |
| aunt (royal92)     |     1.85 |      2.21 |      1.50 |    1.5x |      1.49 |   1.0x |
| n-queens n=7       |     6.40 |      6.05 |      3.27 |    1.8x |      3.26 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     4.77 |      4.66 |      4.64 |    1.0x |      4.64 |   1.0x |
| sliding 3x3 step   |     0.78 |      0.23 |      0.05 |    4.5x |      0.18 |   3.4x |
| gol step 12x12     |     1.31 |      1.42 |      0.56 |    2.5x |      0.56 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.030 |    0.007 |    0.052 |    0.081 |    0.072 |
| datalog tc (n=15)  |    0.791 |    0.215 |    0.014 |    0.138 |    0.026 |
| gol step (glider)  |    0.469 |    1.204 |    0.808 |    0.661 |    0.533 |
| sliding 3x3 step   |    3.607 |    3.204 |    0.373 |    2.409 |    0.697 |
| n-queens n=6       |   21.950 |    2.866 |    1.384 |    2.401 |    2.983 |
| temperature 1024   |    0.095 |    0.034 |    0.036 |    0.076 |    0.046 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.10 |      0.05 |    2.1x |     2 |     1 |
| invariant-inner N=400  |      0.28 |      0.12 |    2.3x |     2 |     1 |
| sliding expandStep 3x3 |      0.49 |      0.13 |    3.7x |    17 |    17 |
| n-queens place(6)      |      1.58 |      1.57 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.7 |       0.5 |       0.3 |     6.2x |    1.8x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      15.1 |       2.4 |       0.7 |    22.1x |    3.5x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     141.9 |      16.0 |       2.3 |    62.7x |    7.1x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    1947.0 |     100.4 |      13.4 |   145.2x |    7.5x |  |
| aunt-query       | family n=150         |      14.3 |       0.9 |       0.2 |    78.6x |    5.0x |  |
| aunt-query       | family n=400         |      94.7 |       5.1 |       0.6 |   164.5x |    8.9x |  |
| aunt-query       | family n=800         |     407.6 |      20.0 |       0.7 |   620.6x |   30.4x |  |
| aunt-query       | family n=1600        |    1774.7 |      79.5 |       1.1 |  1579.1x |   70.7x |  |
| game-of-life     | 16x16 2 steps (68 live) |      26.8 |       7.8 |       5.9 |     4.6x |    1.3x |  |
| game-of-life     | 24x24 2 steps (193 live) |     101.8 |      13.9 |       8.9 |    11.4x |    1.6x |  |
| game-of-life     | 32x32 2 steps (321 live) |     271.7 |      24.8 |      14.4 |    18.9x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   411.1x |    3.6x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1458.6x |    2.9x |  |
| temperature      | 16384 cells (resident) |       1.6 |       0.0 |       0.0 |  6259.7x |    5.2x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      22.6 |       9.7 |       6.4 |     3.5x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     112.3 |      37.2 |      24.9 |     4.5x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.2 |       2.8 |       1.9 |    11.4x |    1.4x |  |
| n-queens         | n=7 (40 sols, pure)  |     119.1 |      12.3 |       6.0 |    19.8x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     693.5 |      55.3 |      26.8 |    25.8x |    2.1x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.1x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.2 |     0.0x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.2 |     0.0x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 59.6x vs the
reference Set, and 3.8x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     12.4 |      0.1 |       0.1 |           0.1 |     0.80 |
| aunt n=400           |      0.2 |     86.5 |      0.3 |       0.2 |           0.2 |     0.83 |
| n-queens n=6         |      1.5 |     23.6 |      3.3 |       3.3 |           0.7 |     0.49 |
| n-queens n=7         |      6.3 |    112.1 |     10.4 |      10.3 |           3.1 |     0.49 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.16 |
| temperature 16384    |      0.0 |      1.7 |      0.0 |       0.0 |           0.0 |     1.67 |
| gol step 12x12       |      1.3 |     11.3 |      1.4 |       1.5 |           0.5 |     0.40 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.51 ms ONCE, run = 0.539 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.539 ms (vs the compiled-in literal, recompiled per grid: 1.05 ms each).

| union_iter           |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     0.71 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.66 |
| datalog tc n=80        |      6.9 |        — |      4.6 |       4.6 |           4.6 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.28 |      0.35 |
| aunt n=400           |      0.00 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.25 |
| n-queens n=6         |      0.11 |     0.41 |     184 |      0.17 |     200 |     0.76 |      1.49 |
| n-queens n=7         |      0.09 |     0.51 |     215 |      0.20 |     234 |     0.86 |      3.95 |
| temperature 4096     |      0.07 |     0.01 |       0 |      0.00 |       1 |     0.10 |      0.10 |
| temperature 16384    |      0.24 |     0.01 |       0 |      0.00 |       1 |     0.26 |      0.26 |
| gol step 12x12       |      0.08 |     0.26 |     102 |      0.11 |     221 |     0.50 |      1.03 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.24 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      4.59 |

**comp+run geomean = 0.477 ms ; run-only geomean = 0.103 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     1.88 |      2.16 |      1.47 |    1.5x |      1.47 |   1.0x |
| n-queens n=7       |     6.54 |      5.82 |      3.07 |    1.9x |      3.06 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     4.75 |      4.63 |      4.59 |    1.0x |      4.58 |   1.0x |
| sliding 3x3 step   |     0.79 |      0.22 |      0.05 |    4.5x |      0.17 |   3.4x |
| gol step 12x12     |     1.33 |      1.38 |      0.54 |    2.6x |      0.53 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.047 |    0.012 |    0.053 |    0.098 |    0.091 |
| datalog tc (n=15)  |    1.272 |    0.260 |    0.019 |    0.190 |    0.040 |
| gol step (glider)  |    0.674 |    1.320 |    0.835 |    0.864 |    0.671 |
| sliding 3x3 step   |    4.800 |    2.813 |    0.030 |    3.564 |    0.930 |
| n-queens n=6       |   25.517 |    3.687 |    1.861 |    2.789 |    3.714 |
| temperature 1024   |    0.113 |    0.039 |    0.044 |    0.089 |    0.054 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.05 |      0.03 |    1.6x |     2 |     1 |
| invariant-inner N=400  |      0.11 |      0.06 |    1.9x |     2 |     1 |
| sliding expandStep 3x3 |      0.25 |      0.07 |    3.6x |    17 |    17 |
| n-queens place(6)      |      0.81 |      0.79 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.4 |       0.5 |       0.2 |     5.9x |    2.0x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.4 |       2.3 |       0.5 |    23.0x |    4.3x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     142.2 |      14.5 |       2.0 |    69.7x |    7.1x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    1936.8 |      99.2 |      13.8 |   140.5x |    7.2x |  |
| aunt-query       | family n=150         |      14.7 |       0.9 |       0.2 |    73.7x |    4.5x |  |
| aunt-query       | family n=400         |      99.2 |       5.1 |       0.3 |   299.3x |   15.4x |  |
| aunt-query       | family n=800         |     418.6 |      19.4 |       0.5 |   770.9x |   35.7x |  |
| aunt-query       | family n=1600        |    1811.1 |      77.3 |       1.1 |  1627.8x |   69.4x |  |
| game-of-life     | 16x16 2 steps (68 live) |      25.0 |       5.6 |       3.7 |     6.7x |    1.5x |  |
| game-of-life     | 24x24 2 steps (193 live) |     103.0 |      13.5 |       8.4 |    12.3x |    1.6x |  |
| game-of-life     | 32x32 2 steps (321 live) |     271.4 |      24.1 |      14.2 |    19.2x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   311.4x |    3.1x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1628.2x |    3.3x |  |
| temperature      | 16384 cells (resident) |       1.6 |       0.0 |       0.0 |  6380.5x |    4.7x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      22.6 |       9.7 |       6.6 |     3.4x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     110.9 |      36.9 |      25.0 |     4.4x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      21.9 |       3.1 |       1.7 |    12.9x |    1.8x |  |
| n-queens         | n=7 (40 sols, pure)  |     121.1 |      11.6 |       4.8 |    25.2x |    2.4x |  |
| n-queens         | n=8 (92 sols, pure)  |     698.1 |      51.3 |      21.4 |    32.6x |    2.4x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.1x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.1 |     0.0x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.2 |     0.0x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 65.3x vs the
reference Set, and 4.1x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     13.8 |      0.1 |       0.1 |           0.1 |     0.80 |
| aunt n=400           |      0.2 |     92.9 |      0.3 |       0.2 |           0.2 |     0.81 |
| n-queens n=6         |      1.2 |     24.3 |      3.4 |       3.4 |           0.7 |     0.61 |
| n-queens n=7         |      5.0 |    114.5 |     10.5 |      10.5 |           3.0 |     0.59 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.33 |
| temperature 16384    |      0.0 |      1.8 |      0.0 |       0.0 |           0.0 |     2.00 |
| gol step 12x12       |      1.3 |     12.0 |      1.5 |       1.5 |           0.5 |     0.40 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.53 ms ONCE, run = 0.532 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.532 ms (vs the compiled-in literal, recompiled per grid: 1.06 ms each).

| union_iter           |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     0.56 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.65 |
| datalog tc n=80        |      5.5 |        — |      3.7 |       3.8 |           3.8 |     0.69 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.04 |       8 |      0.01 |       4 |     0.29 |      0.36 |
| aunt n=400           |      0.00 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.25 |
| n-queens n=6         |      0.11 |     0.43 |     184 |      0.17 |     200 |     0.78 |      1.49 |
| n-queens n=7         |      0.09 |     0.53 |     215 |      0.21 |     234 |     0.90 |      3.87 |
| temperature 4096     |      0.07 |     0.01 |       0 |      0.00 |       1 |     0.10 |      0.10 |
| temperature 16384    |      0.25 |     0.01 |       0 |      0.00 |       1 |     0.27 |      0.27 |
| gol step 12x12       |      0.08 |     0.29 |     102 |      0.11 |     221 |     0.53 |      1.07 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.20 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.03 |      3.80 |

**comp+run geomean = 0.462 ms ; run-only geomean = 0.096 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   0.9x |
| aunt (royal92)     |     1.87 |      2.14 |      1.44 |    1.5x |      1.43 |   1.0x |
| n-queens n=7       |     4.96 |      5.68 |      2.97 |    1.9x |      2.96 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     3.73 |      3.73 |      3.70 |    1.0x |      3.70 |   1.0x |
| sliding 3x3 step   |     0.80 |      0.23 |      0.05 |    4.4x |      0.17 |   3.2x |
| gol step 12x12     |     1.34 |      1.39 |      0.54 |    2.6x |      0.53 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.030 |    0.007 |    0.052 |    0.085 |    0.075 |
| datalog tc (n=15)  |    0.895 |    0.204 |    0.014 |    0.129 |    0.030 |
| gol step (glider)  |    0.470 |    1.194 |    0.806 |    0.675 |    0.556 |
| sliding 3x3 step   |    3.665 |    1.617 |    0.026 |    2.355 |    0.664 |
| n-queens n=6       |   22.291 |    2.401 |    1.392 |    2.249 |    2.873 |
| temperature 1024   |    0.088 |    0.035 |    0.035 |    0.077 |    0.049 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.8x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.05 |    1.9x |     2 |     1 |
| sliding expandStep 3x3 |      1.65 |      0.44 |    3.8x |    17 |    17 |
| n-queens place(6)      |      1.45 |      1.46 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.2 |       0.5 |       0.2 |     5.4x |    2.1x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.9 |       2.4 |       0.5 |    28.3x |    5.3x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     160.4 |      15.2 |       2.3 |    70.9x |    6.7x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2204.0 |     101.9 |      17.0 |   129.9x |    6.0x |  |
| aunt-query       | family n=150         |      15.3 |       0.9 |       0.1 |   175.5x |   10.5x |  |
| aunt-query       | family n=400         |     102.0 |       5.5 |       0.2 |   419.8x |   22.4x |  |
| aunt-query       | family n=800         |     435.5 |      21.1 |       0.7 |   599.1x |   29.0x |  |
| aunt-query       | family n=1600        |    1862.9 |      79.3 |       1.2 |  1617.1x |   68.9x |  |
| game-of-life     | 16x16 2 steps (68 live) |      26.5 |       7.4 |       4.2 |     6.3x |    1.8x |  |
| game-of-life     | 24x24 2 steps (193 live) |     109.8 |      16.3 |       9.6 |    11.5x |    1.7x |  |
| game-of-life     | 32x32 2 steps (321 live) |     292.2 |      29.3 |      17.9 |    16.4x |    1.6x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   406.6x |    4.2x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1932.1x |    6.8x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  6888.2x |    5.2x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      22.2 |       9.9 |       6.5 |     3.4x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     113.9 |      38.1 |      26.0 |     4.4x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.9 |       2.8 |       1.4 |    16.1x |    2.0x |  |
| n-queens         | n=7 (40 sols, pure)  |     135.2 |      12.8 |       6.4 |    21.2x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     744.0 |      57.1 |      27.7 |    26.9x |    2.1x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     0.8x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.1 |     0.0x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.2 |     0.0x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 69.1x vs the
reference Set, and 4.5x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     13.4 |      0.1 |       0.1 |           0.1 |     0.82 |
| aunt n=400           |      0.2 |     93.1 |      0.3 |       0.2 |           0.2 |     0.88 |
| n-queens n=6         |      1.4 |     22.2 |     15.4 |       3.3 |           0.7 |     0.49 |
| n-queens n=7         |      6.5 |    113.2 |     10.7 |      10.5 |           3.0 |     0.47 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.33 |
| temperature 16384    |      0.0 |      1.9 |      0.0 |       0.0 |           0.0 |     2.20 |
| gol step 12x12       |      1.6 |      9.3 |      1.4 |       1.4 |           0.5 |     0.33 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.60 ms ONCE, run = 0.520 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.520 ms (vs the compiled-in literal, recompiled per grid: 1.12 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.56 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.66 |
| datalog tc n=80        |      7.0 |        — |      4.7 |       4.6 |           4.6 |     0.65 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.05 |       8 |      0.02 |       4 |     0.43 |      0.50 |
| aunt n=400           |      0.00 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.12 |     0.51 |     184 |      0.20 |     200 |     0.90 |      1.62 |
| n-queens n=7         |      0.11 |     0.49 |     215 |      0.22 |     234 |     0.88 |      3.93 |
| temperature 4096     |      0.05 |     0.01 |       0 |      0.00 |       1 |     0.07 |      0.07 |
| temperature 16384    |      0.19 |     0.02 |       0 |      0.01 |       1 |     0.22 |      0.22 |
| gol step 12x12       |      0.12 |     0.32 |     102 |      0.12 |     221 |     0.62 |      1.14 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.03 |      0.24 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      4.62 |

**comp+run geomean = 0.483 ms ; run-only geomean = 0.099 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.10 |      2.04 |      1.42 |    1.4x |      1.42 |   1.0x |
| n-queens n=7       |     6.41 |      5.66 |      3.02 |    1.9x |      3.01 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     4.59 |      4.51 |      4.49 |    1.0x |      4.51 |   1.0x |
| sliding 3x3 step   |     0.82 |      0.21 |      0.05 |    4.6x |      0.16 |   3.5x |
| gol step 12x12     |     1.62 |      1.35 |      0.52 |    2.6x |      0.51 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.032 |    0.008 |    0.060 |    0.093 |    0.090 |
| datalog tc (n=15)  |    1.123 |    0.281 |    0.019 |    0.203 |    0.038 |
| gol step (glider)  |    0.730 |    1.894 |    1.281 |    0.833 |    0.665 |
| sliding 3x3 step   |    4.485 |    4.234 |    0.063 |    2.357 |    0.649 |
| n-queens n=6       |   22.934 |    2.918 |    1.452 |    2.228 |    2.833 |
| temperature 1024   |    0.100 |    0.035 |    0.034 |    0.071 |    0.047 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.05 |    1.8x |     2 |     1 |
| sliding expandStep 3x3 |      0.18 |      0.05 |    3.4x |    17 |    17 |
| n-queens place(6)      |      0.84 |      0.78 |    1.1x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.3 |       0.5 |       0.1 |    12.4x |    4.5x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      13.9 |       2.5 |       0.5 |    30.4x |    5.4x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     184.6 |      15.5 |       2.4 |    76.2x |    6.4x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2689.9 |     105.2 |      17.9 |   149.9x |    5.9x |  |
| aunt-query       | family n=150         |      14.9 |       0.9 |       0.1 |   154.4x |    9.9x |  |
| aunt-query       | family n=400         |      96.4 |       5.7 |       0.3 |   370.5x |   21.7x |  |
| aunt-query       | family n=800         |     412.8 |      22.0 |       0.8 |   545.9x |   29.1x |  |
| aunt-query       | family n=1600        |    1770.7 |      85.0 |       1.3 |  1372.1x |   65.9x |  |
| game-of-life     | 16x16 2 steps (68 live) |      26.1 |       7.6 |       4.7 |     5.5x |    1.6x |  |
| game-of-life     | 24x24 2 steps (193 live) |     108.8 |      15.9 |       9.4 |    11.6x |    1.7x |  |
| game-of-life     | 32x32 2 steps (321 live) |     293.3 |      28.6 |      17.9 |    16.3x |    1.6x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   270.4x |    2.4x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1823.7x |    4.2x |  |
| temperature      | 16384 cells (resident) |       1.6 |       0.0 |       0.0 |  6212.8x |    4.2x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.8 |      10.5 |       7.1 |     3.3x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     117.9 |      39.2 |      27.4 |     4.3x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      23.4 |       3.0 |       1.6 |    14.8x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     131.3 |      13.0 |       6.9 |    18.9x |    1.9x |  |
| n-queens         | n=8 (92 sols, pure)  |     784.0 |      63.8 |      32.9 |    23.8x |    1.9x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.6x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     0.8x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.1 |     0.0x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.2 |     0.0x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 67.5x vs the
reference Set, and 4.3x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     13.5 |      0.1 |       0.1 |           0.1 |     0.74 |
| aunt n=400           |      0.3 |     91.2 |      0.3 |       0.2 |           0.2 |     0.79 |
| n-queens n=6         |      1.6 |     21.8 |      3.5 |       3.4 |           0.8 |     0.48 |
| n-queens n=7         |      7.3 |    114.5 |     11.1 |      10.9 |           3.4 |     0.47 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     1.84 |
| temperature 16384    |      0.0 |      1.7 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.6 |      9.8 |     12.6 |       1.5 |           0.6 |     0.35 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.50 ms ONCE, run = 0.553 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.553 ms (vs the compiled-in literal, recompiled per grid: 1.06 ms each).

| union_iter           |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     0.51 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.70 |
| datalog tc n=80        |      7.3 |        — |      4.8 |       4.8 |           4.8 |     0.65 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.33 |      0.40 |
| aunt n=400           |      0.00 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.27 |
| n-queens n=6         |      0.10 |     0.44 |     184 |      0.20 |     200 |     0.81 |      1.59 |
| n-queens n=7         |      0.09 |     0.51 |     215 |      0.23 |     234 |     0.89 |      4.33 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.08 |      0.08 |
| temperature 16384    |      0.23 |     0.01 |       0 |      0.01 |       1 |     0.26 |      0.26 |
| gol step 12x12       |      0.09 |     0.28 |     102 |      0.11 |     221 |     0.53 |      1.09 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.03 |      0.27 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      4.81 |

**comp+run geomean = 0.497 ms ; run-only geomean = 0.105 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.45 |      2.25 |      1.53 |    1.5x |      1.52 |   1.0x |
| n-queens n=7       |     6.71 |      6.11 |      3.33 |    1.8x |      3.26 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     4.90 |      4.82 |      4.74 |    1.0x |      4.74 |   1.0x |
| sliding 3x3 step   |     0.89 |      0.25 |      0.05 |    4.8x |      0.18 |   3.5x |
| gol step 12x12     |     1.59 |      1.40 |      0.55 |    2.6x |      0.55 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.030 |    0.008 |    0.060 |    0.103 |    0.107 |
| datalog tc (n=15)  |    1.366 |    0.239 |    0.038 |    0.194 |    0.076 |
| gol step (glider)  |    0.504 |    1.709 |    1.215 |    0.681 |    0.552 |
| sliding 3x3 step   |    3.803 |    1.790 |    0.052 |    2.466 |    0.654 |
| n-queens n=6       |   23.987 |    3.248 |    1.570 |    2.501 |    3.437 |
| temperature 1024   |    0.241 |    0.071 |    0.035 |    0.077 |    0.048 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.8x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.06 |    1.8x |     2 |     1 |
| sliding expandStep 3x3 |      0.18 |      0.05 |    3.4x |    17 |    17 |
| n-queens place(6)      |      0.74 |      0.74 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.5 |       0.5 |       0.1 |    15.7x |    5.2x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      16.8 |       2.4 |       0.4 |    42.2x |    6.1x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     207.9 |      15.1 |       2.0 |   102.5x |    7.4x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    3258.5 |     102.2 |      15.1 |   216.5x |    6.8x |  |
| aunt-query       | family n=150         |      13.1 |       0.9 |       0.1 |   146.4x |   10.2x |  |
| aunt-query       | family n=400         |      97.6 |       5.3 |       0.2 |   398.9x |   21.5x |  |
| aunt-query       | family n=800         |     421.8 |      20.4 |       0.7 |   616.1x |   29.8x |  |
| aunt-query       | family n=1600        |    1934.2 |      85.2 |       1.2 |  1656.9x |   73.0x |  |
| game-of-life     | 16x16 2 steps (68 live) |      25.4 |       7.8 |       4.5 |     5.7x |    1.7x |  |
| game-of-life     | 24x24 2 steps (193 live) |     106.9 |      16.1 |       9.0 |    11.8x |    1.8x |  |
| game-of-life     | 32x32 2 steps (321 live) |     281.7 |      29.3 |      17.1 |    16.4x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   451.6x |    4.4x |  |
| temperature      | 4096 cells (resident) |       0.5 |       0.0 |       0.0 |  1567.2x |    3.6x |  |
| temperature      | 16384 cells (resident) |       1.8 |       0.0 |       0.0 |  7080.8x |    5.3x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      22.4 |      10.0 |       6.5 |     3.4x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     119.2 |      39.4 |      26.0 |     4.6x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.5 |       2.9 |       1.5 |    15.4x |    2.0x |  |
| n-queens         | n=7 (40 sols, pure)  |     138.0 |      12.9 |       6.4 |    21.6x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     736.9 |      58.1 |      28.1 |    26.2x |    2.1x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     2.0x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.1 |     0.0x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.2 |     0.0x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 76.8x vs the
reference Set, and 4.7x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     12.7 |      0.1 |       0.1 |           0.1 |     0.78 |
| aunt n=400           |      0.2 |     88.6 |      0.3 |       0.2 |           0.2 |     0.85 |
| n-queens n=6         |      1.5 |     21.7 |      3.6 |       3.5 |           0.7 |     0.50 |
| n-queens n=7         |      6.5 |    109.3 |     11.2 |      11.1 |           3.1 |     0.48 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.16 |
| temperature 16384    |      0.0 |      1.8 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.5 |      9.3 |      1.4 |       1.4 |           0.6 |     0.37 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.57 ms ONCE, run = 0.538 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.538 ms (vs the compiled-in literal, recompiled per grid: 1.10 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.57 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.67 |
| datalog tc n=80        |      6.0 |        — |      4.0 |       3.9 |           3.9 |     0.65 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.34 |      0.41 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.25 |
| n-queens n=6         |      0.23 |     0.42 |     184 |      0.17 |     200 |     0.88 |      1.62 |
| n-queens n=7         |      0.11 |     0.49 |     215 |      0.20 |     234 |     0.86 |      3.96 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.08 |      0.08 |
| temperature 16384    |      0.24 |     0.02 |       0 |      0.01 |       1 |     0.27 |      0.27 |
| gol step 12x12       |      0.10 |     0.26 |     102 |      0.11 |     221 |     0.53 |      1.08 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.22 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.03 |      3.93 |

**comp+run geomean = 0.473 ms ; run-only geomean = 0.097 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.01 |      2.17 |      1.46 |    1.5x |      1.45 |   1.0x |
| n-queens n=7       |     6.33 |      5.64 |      3.07 |    1.8x |      3.05 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     3.96 |      3.94 |      3.88 |    1.0x |      3.94 |   1.0x |
| sliding 3x3 step   |     0.82 |      0.22 |      0.05 |    4.4x |      0.17 |   3.3x |
| gol step 12x12     |     1.52 |      1.33 |      0.54 |    2.5x |      0.53 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.088 |    0.008 |    0.119 |    0.078 |    0.073 |
| datalog tc (n=15)  |    1.241 |    0.205 |    0.014 |    0.137 |    0.036 |
| gol step (glider)  |    0.648 |    1.731 |    1.252 |    0.768 |    0.652 |
| sliding 3x3 step   |    4.762 |    2.486 |    0.070 |    3.456 |    0.874 |
| n-queens n=6       |   27.132 |    3.734 |    1.779 |    2.593 |    2.997 |
| temperature 1024   |    0.113 |    0.036 |    0.034 |    0.094 |    0.065 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.11 |      0.06 |    1.8x |     2 |     1 |
| sliding expandStep 3x3 |      0.18 |      0.05 |    3.3x |    17 |    17 |
| n-queens place(6)      |      0.78 |      0.78 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.3 |       0.5 |       0.1 |    13.0x |    4.7x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.8 |       2.4 |       0.4 |    29.0x |    5.4x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     159.8 |      14.9 |       2.3 |    68.3x |    6.4x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2230.3 |     100.8 |      17.1 |   130.7x |    5.9x |  |
| aunt-query       | family n=150         |      14.1 |       0.9 |       0.1 |   152.7x |    9.6x |  |
| aunt-query       | family n=400         |      98.2 |       5.4 |       0.3 |   390.1x |   21.6x |  |
| aunt-query       | family n=800         |     416.4 |      20.3 |       0.7 |   600.7x |   29.3x |  |
| aunt-query       | family n=1600        |    1801.2 |      79.5 |       1.2 |  1554.3x |   68.6x |  |
| game-of-life     | 16x16 2 steps (68 live) |      25.6 |       6.7 |       4.1 |     6.2x |    1.6x |  |
| game-of-life     | 24x24 2 steps (193 live) |     107.5 |      16.1 |       9.5 |    11.3x |    1.7x |  |
| game-of-life     | 32x32 2 steps (321 live) |     279.2 |      28.6 |      16.7 |    16.8x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   391.0x |    3.2x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1812.3x |    4.6x |  |
| temperature      | 16384 cells (resident) |       1.6 |       0.0 |       0.0 |  6507.5x |    5.2x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      22.2 |       9.9 |       6.6 |     3.4x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     113.6 |      39.2 |      26.6 |     4.3x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.9 |       2.8 |       1.5 |    15.2x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     124.1 |      12.5 |       6.5 |    19.0x |    1.9x |  |
| n-queens         | n=8 (92 sols, pure)  |     721.5 |      56.7 |      28.1 |    25.6x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.9x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     0.9x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.0x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.2 |     0.0x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 69.8x vs the
reference Set, and 4.5x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     13.3 |      0.1 |       0.1 |           0.1 |     0.77 |
| aunt n=400           |      0.2 |     92.8 |      0.3 |       0.2 |           0.2 |     0.81 |
| n-queens n=6         |      1.5 |     21.6 |      3.4 |       3.4 |           0.7 |     0.50 |
| n-queens n=7         |      6.3 |    113.1 |     10.7 |      10.6 |           3.2 |     0.50 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.33 |
| temperature 16384    |      0.0 |      1.7 |      0.0 |       0.0 |           0.0 |     1.84 |
| gol step 12x12       |      1.5 |      9.9 |      1.4 |       1.4 |           0.5 |     0.36 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.52 ms ONCE, run = 0.543 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.543 ms (vs the compiled-in literal, recompiled per grid: 1.06 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.54 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.67 |
| datalog tc n=80        |      6.9 |        — |      4.6 |       4.6 |           4.6 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.04 |       8 |      0.01 |       4 |     0.32 |      0.39 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.24 |
| n-queens n=6         |      0.11 |     0.45 |     184 |      0.17 |     200 |     0.79 |      1.53 |
| n-queens n=7         |      0.10 |     0.55 |     215 |      0.22 |     234 |     0.94 |      4.09 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.08 |      0.09 |
| temperature 16384    |      0.24 |     0.02 |       0 |      0.01 |       1 |     0.28 |      0.28 |
| gol step 12x12       |      0.08 |     0.27 |     102 |      0.11 |     221 |     0.52 |      1.06 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.24 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      4.61 |

**comp+run geomean = 0.480 ms ; run-only geomean = 0.099 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.6x |      0.00 |   1.0x |
| aunt (royal92)     |     2.09 |      2.08 |      1.41 |    1.5x |      1.41 |   1.0x |
| n-queens n=7       |     6.37 |      5.64 |      3.13 |    1.8x |      3.10 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     4.62 |      4.57 |      4.56 |    1.0x |      4.60 |   1.0x |
| sliding 3x3 step   |     0.85 |      0.22 |      0.05 |    4.4x |      0.17 |   3.3x |
| gol step 12x12     |     1.61 |      1.35 |      0.54 |    2.5x |      0.54 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.041 |    0.008 |    0.060 |    0.089 |    0.133 |
| datalog tc (n=15)  |    0.998 |    0.227 |    0.015 |    0.160 |    0.036 |
| gol step (glider)  |    0.587 |    1.757 |    1.238 |    0.748 |    0.603 |
| sliding 3x3 step   |    4.795 |    2.647 |    0.068 |    3.460 |    0.905 |
| n-queens n=6       |   26.894 |    3.066 |    1.437 |    2.322 |    3.040 |
| temperature 1024   |    0.098 |    0.034 |    0.033 |    0.076 |    0.049 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.11 |      0.06 |    1.8x |     2 |     1 |
| sliding expandStep 3x3 |      0.19 |      0.05 |    3.5x |    17 |    17 |
| n-queens place(6)      |      0.79 |      0.79 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.3 |       0.5 |       0.2 |     5.5x |    2.1x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.6 |       2.4 |       0.5 |    27.9x |    5.2x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     157.4 |      15.3 |       2.5 |    63.3x |    6.2x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2188.0 |     100.3 |      18.4 |   119.0x |    5.5x |  |
| aunt-query       | family n=150         |      14.0 |       0.8 |       0.1 |   161.9x |    9.7x |  |
| aunt-query       | family n=400         |     103.2 |       5.1 |       0.2 |   432.5x |   21.4x |  |
| aunt-query       | family n=800         |     433.9 |      20.3 |       0.7 |   605.0x |   28.3x |  |
| aunt-query       | family n=1600        |    1889.8 |      90.3 |       1.2 |  1627.3x |   77.8x |  |
| game-of-life     | 16x16 2 steps (68 live) |      25.8 |       6.7 |       3.7 |     7.0x |    1.8x |  |
| game-of-life     | 24x24 2 steps (193 live) |     109.4 |      15.8 |       9.2 |    12.0x |    1.7x |  |
| game-of-life     | 32x32 2 steps (321 live) |     284.7 |      29.3 |      16.4 |    17.4x |    1.8x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   389.0x |    3.8x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1510.5x |    4.0x |  |
| temperature      | 16384 cells (resident) |       1.6 |       0.0 |       0.0 |  6217.7x |    5.0x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.2 |      10.2 |       6.9 |     3.3x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     114.7 |      39.3 |      26.4 |     4.4x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.7 |       2.8 |       1.5 |    14.9x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     128.6 |      13.0 |       6.6 |    19.4x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     746.8 |      58.8 |      29.8 |    25.1x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     2.1x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     0.8x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.1 |     0.0x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.2 |     0.0x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 66.6x vs the
reference Set, and 4.3x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     12.9 |      0.1 |       0.1 |           0.1 |     0.84 |
| aunt n=400           |      0.2 |     90.7 |      0.3 |       0.2 |           0.2 |     0.82 |
| n-queens n=6         |      1.6 |     22.0 |      3.8 |       3.7 |           0.8 |     0.49 |
| n-queens n=7         |      6.6 |    111.9 |     11.8 |      11.7 |           3.3 |     0.50 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.33 |
| temperature 16384    |      0.0 |      1.6 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.6 |     12.6 |      1.6 |       1.6 |           0.6 |     0.36 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.52 ms ONCE, run = 0.565 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.565 ms (vs the compiled-in literal, recompiled per grid: 1.09 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.70 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.67 |
| datalog tc n=80        |      7.5 |        — |      5.0 |       5.0 |           5.0 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.28 |      0.36 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.11 |     0.43 |     184 |      0.18 |     200 |     0.78 |      1.56 |
| n-queens n=7         |      0.10 |     0.54 |     215 |      0.23 |     234 |     0.95 |      4.27 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.01 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.24 |     0.02 |       0 |      0.01 |       1 |     0.28 |      0.28 |
| gol step 12x12       |      0.09 |     0.28 |     102 |      0.11 |     221 |     0.53 |      1.10 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.26 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      5.01 |

**comp+run geomean = 0.495 ms ; run-only geomean = 0.107 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.13 |      2.39 |      1.57 |    1.5x |      1.59 |   1.0x |
| n-queens n=7       |     6.58 |      6.28 |      3.31 |    1.9x |      3.32 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     5.10 |      5.05 |      4.99 |    1.0x |      5.05 |   1.0x |
| sliding 3x3 step   |     0.85 |      0.24 |      0.06 |    4.2x |      0.18 |   3.1x |
| gol step 12x12     |     1.52 |      1.44 |      0.56 |    2.6x |      0.56 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.036 |    0.007 |    0.058 |    0.100 |    0.077 |
| datalog tc (n=15)  |    0.853 |    0.223 |    0.014 |    0.152 |    0.029 |
| gol step (glider)  |    0.484 |    1.730 |    1.198 |    0.663 |    0.550 |
| sliding 3x3 step   |    3.650 |    1.715 |    0.047 |    2.364 |    0.665 |
| n-queens n=6       |   23.372 |    3.084 |    1.465 |    2.433 |    3.010 |
| temperature 1024   |    0.098 |    0.033 |    0.033 |    0.072 |    0.047 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.06 |    1.8x |     2 |     1 |
| sliding expandStep 3x3 |      0.18 |      0.05 |    3.3x |    17 |    17 |
| n-queens place(6)      |      0.75 |      0.74 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.3 |       0.5 |       0.1 |    10.4x |    3.9x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      14.8 |       2.5 |       0.4 |    34.7x |    5.8x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     174.1 |      16.3 |       2.1 |    81.4x |    7.6x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2496.9 |     109.5 |      15.1 |   165.1x |    7.2x |  |
| aunt-query       | family n=150         |      15.4 |       0.9 |       0.1 |   167.7x |    9.9x |  |
| aunt-query       | family n=400         |     124.6 |       5.6 |       0.3 |   456.2x |   20.4x |  |
| aunt-query       | family n=800         |     412.1 |      20.4 |       0.7 |   581.3x |   28.8x |  |
| aunt-query       | family n=1600        |    1921.2 |      78.7 |       1.2 |  1660.0x |   68.0x |  |
| game-of-life     | 16x16 2 steps (68 live) |      25.9 |       7.2 |       4.4 |     5.8x |    1.6x |  |
| game-of-life     | 24x24 2 steps (193 live) |     132.0 |      18.5 |      10.0 |    13.3x |    1.9x |  |
| game-of-life     | 32x32 2 steps (321 live) |     296.3 |      28.8 |      17.8 |    16.7x |    1.6x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   437.5x |    3.2x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1954.9x |    5.2x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  5094.8x |    3.6x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.3 |      10.2 |       6.9 |     3.4x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     115.4 |      39.0 |      27.1 |     4.3x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.6 |       2.8 |       1.5 |    15.0x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     133.6 |      13.1 |       6.5 |    20.4x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     735.6 |      58.1 |      28.9 |    25.4x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.9x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.1 |     0.0x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.2 |     0.0x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 72.6x vs the
reference Set, and 4.5x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     13.0 |      0.1 |       0.1 |           0.1 |     0.78 |
| aunt n=400           |      0.2 |     92.6 |      0.3 |       0.2 |           0.2 |     0.81 |
| n-queens n=6         |      1.5 |     22.1 |     15.4 |       3.3 |           0.8 |     0.50 |
| n-queens n=7         |      7.1 |    113.4 |     10.6 |      10.5 |           3.1 |     0.44 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.33 |
| temperature 16384    |      0.0 |      1.8 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.6 |      9.4 |      1.4 |       1.5 |           0.5 |     0.35 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.50 ms ONCE, run = 0.541 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.541 ms (vs the compiled-in literal, recompiled per grid: 1.04 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.49 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.66 |
| datalog tc n=80        |      5.9 |        — |      4.1 |       4.2 |           4.2 |     0.71 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.29 |      0.36 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.11 |     1.28 |     184 |      0.19 |     200 |     1.64 |      2.39 |
| n-queens n=7         |      0.10 |     0.53 |     215 |      0.21 |     234 |     0.91 |      4.03 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.08 |      0.08 |
| temperature 16384    |      0.22 |     0.02 |       0 |      0.01 |       1 |     0.26 |      0.26 |
| gol step 12x12       |      0.08 |     0.26 |     102 |      0.11 |     221 |     0.50 |      1.05 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.21 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      4.22 |

**comp+run geomean = 0.483 ms ; run-only geomean = 0.098 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.21 |      2.16 |      1.48 |    1.5x |      1.47 |   1.0x |
| n-queens n=7       |     6.57 |      5.76 |      3.11 |    1.9x |      3.11 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     4.02 |      3.87 |      3.85 |    1.0x |      3.85 |   1.0x |
| sliding 3x3 step   |     0.86 |      0.22 |      0.05 |    4.4x |      0.17 |   3.2x |
| gol step 12x12     |     1.56 |      1.36 |      0.54 |    2.5x |      0.54 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.049 |    0.010 |    0.062 |    0.105 |    0.097 |
| datalog tc (n=15)  |    1.256 |    0.271 |    0.018 |    0.189 |    0.037 |
| gol step (glider)  |    0.819 |    1.710 |    1.204 |    0.896 |    0.707 |
| sliding 3x3 step   |    4.009 |    2.559 |    0.078 |    3.671 |    0.874 |
| n-queens n=6       |   29.566 |    3.799 |    1.938 |    2.819 |    4.788 |
| temperature 1024   |    0.115 |    0.059 |    0.049 |    0.090 |    0.062 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    2.0x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.05 |    1.9x |     2 |     1 |
| sliding expandStep 3x3 |      1.74 |      0.47 |    3.7x |    17 |    17 |
| n-queens place(6)      |      1.48 |      1.48 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.3 |       0.5 |       0.1 |    13.4x |    5.2x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      13.5 |       2.5 |       0.4 |    32.5x |    6.1x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     163.1 |      15.8 |       2.0 |    81.7x |    7.9x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2324.2 |     109.8 |      13.5 |   171.8x |    8.1x |  |
| aunt-query       | family n=150         |      13.7 |       0.9 |       0.1 |   149.2x |   10.0x |  |
| aunt-query       | family n=400         |      99.5 |       5.2 |       0.3 |   355.4x |   18.7x |  |
| aunt-query       | family n=800         |     436.6 |      21.2 |       0.7 |   620.7x |   30.1x |  |
| aunt-query       | family n=1600        |    1876.7 |      83.2 |       1.2 |  1539.1x |   68.3x |  |
| game-of-life     | 16x16 2 steps (68 live) |      29.4 |       9.0 |       5.8 |     5.1x |    1.6x |  |
| game-of-life     | 24x24 2 steps (193 live) |     112.1 |      16.2 |       9.9 |    11.3x |    1.6x |  |
| game-of-life     | 32x32 2 steps (321 live) |     288.6 |      30.7 |      18.1 |    15.9x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   460.7x |    3.4x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1653.2x |    3.7x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  5018.5x |    3.5x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.9 |      10.7 |       7.2 |     3.3x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     119.2 |      45.0 |      29.2 |     4.1x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      23.9 |       3.5 |       1.6 |    15.4x |    2.3x |  |
| n-queens         | n=7 (40 sols, pure)  |     131.9 |      13.3 |       6.6 |    20.0x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     762.8 |      63.9 |      30.7 |    24.9x |    2.1x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     2.3x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 70.0x vs the
reference Set, and 4.6x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     12.9 |      0.1 |       0.1 |           0.1 |     0.81 |
| aunt n=400           |      0.3 |     87.6 |      0.3 |       0.2 |           0.2 |     0.81 |
| n-queens n=6         |      1.5 |     22.0 |      3.7 |       3.7 |           0.7 |     0.48 |
| n-queens n=7         |      6.7 |    109.9 |     11.5 |      10.9 |           3.0 |     0.44 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     1.83 |
| temperature 16384    |      0.0 |      1.8 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.7 |      9.3 |      1.4 |       1.4 |           0.5 |     0.29 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.52 ms ONCE, run = 0.498 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.498 ms (vs the compiled-in literal, recompiled per grid: 1.01 ms each).

| union_iter           |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     0.58 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.66 |
| datalog tc n=80        |      5.5 |        — |      3.6 |       3.8 |           3.8 |     0.68 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.31 |      0.38 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.24 |     0.44 |     184 |      0.18 |     200 |     0.93 |      1.64 |
| n-queens n=7         |      0.10 |     0.54 |     215 |      0.21 |     234 |     0.92 |      3.88 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.08 |      0.08 |
| temperature 16384    |      0.23 |     0.02 |       0 |      0.01 |       1 |     0.27 |      0.27 |
| gol step 12x12       |      0.09 |     0.27 |     102 |      0.11 |     221 |     0.52 |      1.02 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.21 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      3.79 |

**comp+run geomean = 0.461 ms ; run-only geomean = 0.097 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.31 |      2.21 |      1.49 |    1.5x |      1.49 |   1.0x |
| n-queens n=7       |     6.71 |      5.57 |      2.99 |    1.9x |      2.97 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     3.86 |      3.71 |      3.67 |    1.0x |      3.64 |   1.0x |
| sliding 3x3 step   |     0.88 |      0.22 |      0.05 |    4.4x |      0.17 |   3.3x |
| gol step 12x12     |     1.43 |      1.27 |      0.50 |    2.5x |      0.50 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.031 |    0.008 |    0.059 |    0.078 |    0.074 |
| datalog tc (n=15)  |    0.862 |    0.205 |    0.014 |    0.135 |    0.031 |
| gol step (glider)  |    0.501 |    1.711 |    1.200 |    0.747 |    0.552 |
| sliding 3x3 step   |    4.139 |    1.885 |    0.049 |    2.494 |    0.741 |
| n-queens n=6       |   24.911 |    3.021 |    1.400 |    2.393 |    2.936 |
| temperature 1024   |    0.109 |    0.036 |    0.036 |    0.076 |    0.050 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.8x |     2 |     1 |
| invariant-inner N=400  |      0.11 |      0.06 |    1.8x |     2 |     1 |
| sliding expandStep 3x3 |      0.19 |      0.06 |    3.4x |    17 |    17 |
| n-queens place(6)      |      0.78 |      0.78 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.3 |       0.5 |       0.1 |    13.2x |    4.8x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      14.4 |       2.6 |       0.4 |    33.8x |    6.2x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     183.3 |      15.0 |       2.0 |    89.6x |    7.3x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2644.1 |     102.5 |      15.0 |   176.6x |    6.8x |  |
| aunt-query       | family n=150         |      13.6 |       1.0 |       0.1 |   145.0x |   10.9x |  |
| aunt-query       | family n=400         |      90.2 |       5.4 |       0.3 |   342.5x |   20.6x |  |
| aunt-query       | family n=800         |     401.9 |      19.7 |       0.7 |   546.2x |   26.8x |  |
| aunt-query       | family n=1600        |    1750.1 |      78.0 |       1.2 |  1453.8x |   64.8x |  |
| game-of-life     | 16x16 2 steps (68 live) |      24.3 |       6.8 |       4.1 |     6.0x |    1.7x |  |
| game-of-life     | 24x24 2 steps (193 live) |     102.7 |      15.4 |       9.2 |    11.2x |    1.7x |  |
| game-of-life     | 32x32 2 steps (321 live) |     280.2 |      28.7 |      16.8 |    16.7x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   416.9x |    3.8x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1326.8x |    2.9x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  6766.0x |    4.0x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.3 |      10.3 |       7.0 |     3.3x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     113.5 |      39.1 |      26.7 |     4.3x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.5 |       3.5 |       1.6 |    14.1x |    2.2x |  |
| n-queens         | n=7 (40 sols, pure)  |     126.1 |      13.3 |       6.7 |    18.7x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     721.7 |      59.6 |      30.8 |    23.4x |    1.9x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.1x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 69.6x vs the
reference Set, and 4.5x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     13.1 |      0.1 |       0.1 |           0.1 |     0.77 |
| aunt n=400           |      0.3 |     93.9 |      0.3 |       0.2 |           0.2 |     0.78 |
| n-queens n=6         |      1.5 |     21.9 |      3.4 |       3.4 |           0.8 |     0.51 |
| n-queens n=7         |      6.6 |    112.0 |     10.8 |      10.6 |           3.2 |     0.48 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     1.83 |
| temperature 16384    |      0.0 |      1.9 |      0.0 |       0.0 |           0.0 |     2.20 |
| gol step 12x12       |      1.5 |     10.6 |      1.4 |       1.4 |           0.5 |     0.32 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.52 ms ONCE, run = 0.495 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.495 ms (vs the compiled-in literal, recompiled per grid: 1.02 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.58 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.68 |
| datalog tc n=80        |      6.0 |        — |      4.0 |       4.0 |           4.0 |     0.67 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.32 |      0.39 |
| aunt n=400           |      0.00 |     0.05 |       8 |      0.01 |       4 |     0.08 |      0.27 |
| n-queens n=6         |      0.10 |     0.42 |     184 |      0.17 |     200 |     0.76 |      1.52 |
| n-queens n=7         |      0.09 |     0.52 |     215 |      0.22 |     234 |     0.89 |      4.10 |
| temperature 4096     |      0.07 |     0.01 |       0 |      0.00 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.26 |     0.02 |       0 |      0.01 |       1 |     0.30 |      0.30 |
| gol step 12x12       |      0.08 |     0.27 |     102 |      0.11 |     221 |     0.51 |      1.00 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.03 |      0.23 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      4.01 |

**comp+run geomean = 0.482 ms ; run-only geomean = 0.099 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.16 |      2.28 |      1.54 |    1.5x |      1.51 |   1.0x |
| n-queens n=7       |     6.66 |      5.96 |      3.20 |    1.9x |      3.23 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     4.11 |      3.95 |      3.95 |    1.0x |      3.93 |   1.0x |
| sliding 3x3 step   |     0.86 |      0.23 |      0.05 |    4.3x |      0.17 |   3.2x |
| gol step 12x12     |     1.51 |      1.28 |      0.49 |    2.6x |      0.49 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.034 |    0.008 |    0.059 |    0.081 |    0.075 |
| datalog tc (n=15)  |    0.880 |    0.212 |    0.014 |    0.135 |    0.029 |
| gol step (glider)  |    0.465 |    1.692 |    1.195 |    0.651 |    0.530 |
| sliding 3x3 step   |    3.807 |    1.731 |    0.071 |    3.475 |    0.909 |
| n-queens n=6       |   27.958 |    3.116 |    1.634 |    2.425 |    3.144 |
| temperature 1024   |    0.117 |    0.037 |    0.037 |    0.079 |    0.051 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.05 |    1.9x |     2 |     1 |
| sliding expandStep 3x3 |      0.18 |      0.05 |    3.4x |    17 |    17 |
| n-queens place(6)      |      0.72 |      0.72 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.3 |       0.5 |       0.1 |    12.5x |    4.9x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.6 |       2.4 |       0.4 |    32.4x |    6.2x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     158.0 |      15.5 |       1.9 |    81.2x |    8.0x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2198.8 |     105.1 |      13.8 |   159.2x |    7.6x |  |
| aunt-query       | family n=150         |      14.9 |       0.9 |       0.1 |   159.4x |   10.0x |  |
| aunt-query       | family n=400         |      97.7 |       5.3 |       0.3 |   377.6x |   20.6x |  |
| aunt-query       | family n=800         |     412.1 |      20.7 |       0.7 |   581.0x |   29.1x |  |
| aunt-query       | family n=1600        |    1781.1 |      79.7 |       1.2 |  1505.0x |   67.4x |  |
| game-of-life     | 16x16 2 steps (68 live) |      25.9 |       6.4 |       4.0 |     6.5x |    1.6x |  |
| game-of-life     | 24x24 2 steps (193 live) |     109.4 |      14.9 |       9.1 |    12.0x |    1.6x |  |
| game-of-life     | 32x32 2 steps (321 live) |     286.3 |      26.7 |      15.5 |    18.4x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   419.7x |    3.2x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1943.7x |    4.8x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  6882.0x |    5.0x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      26.2 |      10.4 |       7.1 |     3.7x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     114.9 |      39.0 |      27.1 |     4.2x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.9 |       2.9 |       1.5 |    15.3x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     128.4 |      12.9 |       6.5 |    19.8x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     741.0 |      57.7 |      28.4 |    26.1x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.1x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.1x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.1x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 73.3x vs the
reference Set, and 4.6x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     14.3 |      0.1 |       0.1 |           0.1 |     0.76 |
| aunt n=400           |      0.3 |     99.8 |      0.3 |       0.2 |           0.2 |     0.78 |
| n-queens n=6         |      1.5 |     22.6 |      3.8 |       3.7 |           0.7 |     0.46 |
| n-queens n=7         |      6.4 |    115.0 |     11.6 |      11.5 |           3.0 |     0.47 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.80 |
| temperature 16384    |      0.0 |      1.9 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.5 |     10.1 |      1.4 |       1.4 |           0.5 |     0.34 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.52 ms ONCE, run = 0.498 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.498 ms (vs the compiled-in literal, recompiled per grid: 1.02 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.52 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.66 |
| datalog tc n=80        |      5.6 |        — |      3.7 |       3.6 |           3.6 |     0.65 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.34 |      0.41 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.24 |     0.44 |     184 |      0.17 |     200 |     0.92 |      1.63 |
| n-queens n=7         |      0.11 |     0.53 |     215 |      0.21 |     234 |     0.90 |      3.93 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.08 |      0.08 |
| temperature 16384    |      0.24 |     0.02 |       0 |      0.01 |       1 |     0.27 |      0.27 |
| gol step 12x12       |      0.11 |     0.26 |     102 |      0.11 |     221 |     0.54 |      1.04 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.21 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.01 |       0 |     0.03 |      3.67 |

**comp+run geomean = 0.466 ms ; run-only geomean = 0.095 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.40 |      2.30 |      1.55 |    1.5x |      1.51 |   1.0x |
| n-queens n=7       |     6.50 |      5.73 |      3.07 |    1.9x |      3.05 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     3.95 |      3.68 |      3.67 |    1.0x |      3.70 |   1.0x |
| sliding 3x3 step   |     0.85 |      0.22 |      0.04 |    4.8x |      0.17 |   3.7x |
| gol step 12x12     |     1.42 |      1.27 |      0.49 |    2.6x |      0.49 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.042 |    0.011 |    0.061 |    0.093 |    0.092 |
| datalog tc (n=15)  |    1.173 |    0.256 |    0.017 |    0.187 |    0.035 |
| gol step (glider)  |    0.664 |    1.910 |    1.279 |    0.870 |    0.738 |
| sliding 3x3 step   |    4.777 |    2.460 |    0.065 |    3.134 |    0.791 |
| n-queens n=6       |   26.919 |    3.855 |    1.856 |    2.970 |    4.144 |
| temperature 1024   |    0.130 |    0.047 |    0.041 |    0.096 |    0.059 |

## Loop-invariant subgraph hoisting — A/B (2026-06-27)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.12 |      0.06 |    1.9x |     2 |     1 |
| sliding expandStep 3x3 |      0.21 |      0.06 |    3.4x |    17 |    17 |
| n-queens place(6)      |      0.85 |      0.85 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-27)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.6 |       0.5 |       0.1 |    15.6x |    5.2x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      16.3 |       2.8 |       0.5 |    35.6x |    6.2x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     195.5 |      16.5 |       2.1 |    92.9x |    7.9x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2831.9 |     119.9 |      15.9 |   178.4x |    7.6x |  |
| aunt-query       | family n=150         |      16.7 |       1.0 |       0.1 |   162.7x |    9.5x |  |
| aunt-query       | family n=400         |     106.0 |       5.7 |       0.3 |   376.9x |   20.3x |  |
| aunt-query       | family n=800         |     425.7 |      33.1 |       1.1 |   390.6x |   30.3x |  |
| aunt-query       | family n=1600        |    1826.6 |      87.2 |       1.3 |  1410.4x |   67.4x |  |
| game-of-life     | 16x16 2 steps (68 live) |      30.1 |       8.0 |       4.7 |     6.4x |    1.7x |  |
| game-of-life     | 24x24 2 steps (193 live) |     120.0 |      16.5 |       9.8 |    12.3x |    1.7x |  |
| game-of-life     | 32x32 2 steps (321 live) |     287.9 |      27.7 |      16.3 |    17.7x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   344.5x |    3.0x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1877.4x |    4.6x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  6836.3x |    5.0x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      22.1 |      10.1 |       6.7 |     3.3x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     111.3 |      38.3 |      25.6 |     4.3x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.3 |       2.9 |       1.5 |    15.1x |    2.0x |  |
| n-queens         | n=7 (40 sols, pure)  |     124.9 |      12.6 |       6.3 |    19.7x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     790.3 |      62.9 |      31.9 |    24.7x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     2.2x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 72.1x vs the
reference Set, and 4.6x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-27)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     14.0 |      0.1 |       0.1 |           0.1 |     0.78 |
| aunt n=400           |      0.2 |    102.4 |      0.3 |       0.2 |           0.2 |     0.80 |
| n-queens n=6         |      1.5 |     27.8 |      4.2 |       4.1 |           0.9 |     0.58 |
| n-queens n=7         |      8.1 |    125.4 |     12.1 |      11.5 |           3.3 |     0.41 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.00 |
| temperature 16384    |      0.0 |      2.0 |      0.0 |       0.0 |           0.0 |     1.72 |
| gol step 12x12       |      1.6 |     10.7 |      1.5 |       1.6 |           0.5 |     0.34 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.57 ms ONCE, run = 0.540 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.540 ms (vs the compiled-in literal, recompiled per grid: 1.11 ms each).

| union_iter           |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     0.57 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.67 |
| datalog tc n=80        |      6.1 |        — |      4.1 |       4.0 |           4.0 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.29 |      0.36 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.05 |      0.25 |
| n-queens n=6         |      0.23 |     0.42 |     184 |      0.16 |     200 |     0.88 |      1.77 |
| n-queens n=7         |      0.11 |     0.61 |     215 |      0.24 |     234 |     1.04 |      4.34 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.26 |     0.02 |       0 |      0.01 |       1 |     0.31 |      0.31 |
| gol step 12x12       |      0.09 |     0.29 |     102 |      0.11 |     221 |     0.55 |      1.08 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.24 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      4.06 |

**comp+run geomean = 0.491 ms ; run-only geomean = 0.102 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-27)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.10 |      2.27 |      1.51 |    1.5x |      1.51 |   1.0x |
| n-queens n=7       |     6.58 |      5.82 |      3.18 |    1.8x |      3.10 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     4.05 |      3.97 |      3.97 |    1.0x |      3.91 |   1.0x |
| sliding 3x3 step   |     0.88 |      0.23 |      0.05 |    4.5x |      0.17 |   3.4x |
| gol step 12x12     |     1.54 |      1.32 |      0.51 |    2.6x |      0.50 |   1.0x |

## Pipeline-stage ablation (2026-06-27)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.055 |    0.011 |    0.081 |    0.161 |    0.106 |
| datalog tc (n=15)  |    1.477 |    0.439 |    0.027 |    0.234 |    0.045 |
| gol step (glider)  |    0.778 |    2.647 |    1.768 |    1.041 |    1.024 |
| sliding 3x3 step   |    5.833 |    4.000 |    0.081 |    4.116 |    1.083 |
| n-queens n=6       |   37.100 |    5.202 |    2.327 |    2.924 |    3.590 |
| temperature 1024   |    0.121 |    0.041 |    0.040 |    0.089 |    0.056 |

## Loop-invariant subgraph hoisting — A/B (2026-06-28)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    2.0x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.05 |    2.0x |     2 |     1 |
| sliding expandStep 3x3 |      1.72 |      0.46 |    3.8x |    17 |    17 |
| n-queens place(6)      |      1.55 |      1.53 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-28)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.3 |       0.5 |       0.3 |     4.9x |    1.9x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      13.2 |       2.7 |       0.5 |    28.6x |    5.9x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     159.3 |      17.5 |       2.4 |    65.9x |    7.2x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2297.4 |     114.3 |      15.8 |   145.2x |    7.2x |  |
| aunt-query       | family n=150         |      15.2 |       1.0 |       0.1 |   158.3x |   10.1x |  |
| aunt-query       | family n=400         |     124.9 |       5.4 |       0.3 |   480.9x |   20.8x |  |
| aunt-query       | family n=800         |     446.4 |      21.6 |       0.8 |   558.4x |   27.0x |  |
| aunt-query       | family n=1600        |    2018.5 |      82.3 |       1.4 |  1416.7x |   57.7x |  |
| game-of-life     | 16x16 2 steps (68 live) |      28.3 |       7.2 |       4.4 |     6.4x |    1.6x |  |
| game-of-life     | 24x24 2 steps (193 live) |     115.0 |      15.4 |       9.6 |    12.0x |    1.6x |  |
| game-of-life     | 32x32 2 steps (321 live) |     300.0 |      27.8 |      17.5 |    17.2x |    1.6x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   517.0x |    4.0x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1959.7x |    3.8x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  4514.6x |    3.3x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      24.1 |      10.3 |       7.3 |     3.3x |    1.4x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     122.4 |      40.5 |      28.3 |     4.3x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      26.1 |       3.2 |       1.7 |    15.4x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     156.7 |      13.6 |       7.0 |    22.5x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |    1011.5 |     112.9 |      31.8 |    31.8x |    3.5x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     2.1x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     0.9x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 68.6x vs the
reference Set, and 4.3x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-28)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     14.2 |      0.1 |       0.1 |           0.1 |     0.78 |
| aunt n=400           |      0.3 |    100.6 |      0.3 |       0.2 |           0.2 |     0.78 |
| n-queens n=6         |      1.6 |     25.3 |      3.6 |       3.6 |           0.8 |     0.47 |
| n-queens n=7         |      6.9 |    131.0 |     11.2 |      11.0 |           3.4 |     0.49 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     1.83 |
| temperature 16384    |      0.0 |      2.1 |      0.0 |       0.0 |           0.0 |     4.16 |
| gol step 12x12       |      1.5 |      9.8 |      1.5 |       1.5 |           0.5 |     0.34 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.55 ms ONCE, run = 0.513 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.513 ms (vs the compiled-in literal, recompiled per grid: 1.06 ms each).

| union_iter           |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     0.52 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.67 |
| datalog tc n=80        |      6.4 |        — |      4.2 |       4.2 |           4.2 |     0.65 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.02 |     0.04 |       8 |      0.02 |       4 |     0.42 |      0.50 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.27 |
| n-queens n=6         |      0.24 |     0.44 |     184 |      0.21 |     200 |     0.96 |      1.73 |
| n-queens n=7         |      0.10 |     0.54 |     215 |      0.22 |     234 |     0.93 |      4.32 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.01 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.24 |     0.01 |       0 |      0.00 |       1 |     0.27 |      0.27 |
| gol step 12x12       |      0.09 |     0.28 |     102 |      0.12 |     221 |     0.58 |      1.10 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.04 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.03 |      0.24 |
| datalog tc n=80        |      0.03 |     0.01 |       0 |      0.00 |       0 |     0.05 |      4.22 |

**comp+run geomean = 0.508 ms ; run-only geomean = 0.100 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-28)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.47 |      2.37 |      1.48 |    1.6x |      1.48 |   1.0x |
| n-queens n=7       |     6.95 |      6.39 |      3.42 |    1.9x |      3.40 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     4.37 |      4.26 |      4.24 |    1.0x |      4.24 |   1.0x |
| sliding 3x3 step   |     0.89 |      0.24 |      0.05 |    4.5x |      0.17 |   3.3x |
| gol step 12x12     |     1.52 |      1.39 |      0.51 |    2.7x |      0.51 |   1.0x |

## Pipeline-stage ablation (2026-06-28)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.051 |    0.013 |    0.076 |    0.113 |    0.134 |
| datalog tc (n=15)  |    1.803 |    0.315 |    0.037 |    0.217 |    0.035 |
| gol step (glider)  |    1.146 |    2.028 |    1.349 |    1.073 |    0.826 |
| sliding 3x3 step   |    5.618 |    3.497 |    0.082 |    4.460 |    1.111 |
| n-queens n=6       |   41.410 |    4.888 |    3.317 |    4.107 |    5.727 |
| temperature 1024   |    0.110 |    0.035 |    0.043 |    0.082 |    0.057 |

## Loop-invariant subgraph hoisting — A/B (2026-06-28)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    2.0x |     2 |     1 |
| invariant-inner N=400  |      0.11 |      0.06 |    1.8x |     2 |     1 |
| sliding expandStep 3x3 |      0.18 |      0.05 |    3.4x |    17 |    17 |
| n-queens place(6)      |      0.79 |      0.77 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-28)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.2 |       0.5 |       0.2 |     5.4x |    2.0x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.3 |       2.3 |       0.4 |    28.0x |    5.3x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     155.2 |      14.8 |       2.4 |    65.2x |    6.2x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2135.4 |     100.6 |      17.4 |   123.0x |    5.8x |  |
| aunt-query       | family n=150         |      13.4 |       0.9 |       0.1 |   151.8x |   10.0x |  |
| aunt-query       | family n=400         |      95.4 |       5.3 |       0.2 |   394.7x |   21.8x |  |
| aunt-query       | family n=800         |     418.0 |      21.4 |       0.7 |   588.0x |   30.1x |  |
| aunt-query       | family n=1600        |    1934.5 |      82.1 |       1.2 |  1575.7x |   66.8x |  |
| game-of-life     | 16x16 2 steps (68 live) |      27.8 |       5.9 |       3.7 |     7.5x |    1.6x |  |
| game-of-life     | 24x24 2 steps (193 live) |     109.7 |      14.7 |       8.7 |    12.6x |    1.7x |  |
| game-of-life     | 32x32 2 steps (321 live) |     302.1 |      26.9 |      16.4 |    18.4x |    1.6x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   420.9x |    4.2x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1377.0x |    3.4x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  6696.2x |    5.2x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.1 |      10.2 |       6.8 |     3.4x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     123.7 |      48.2 |      26.8 |     4.6x |    1.8x |  |
| n-queens         | n=6 (4 sols, pure)   |      24.4 |       3.0 |       1.6 |    15.4x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     142.2 |      13.4 |       6.8 |    21.0x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     732.8 |      56.3 |      29.0 |    25.3x |    1.9x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     0.8x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     0.8x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 67.6x vs the
reference Set, and 4.3x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-28)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     13.8 |      0.1 |       0.1 |           0.1 |     0.80 |
| aunt n=400           |      0.2 |     93.3 |      0.3 |       0.2 |           0.2 |     0.82 |
| n-queens n=6         |      1.5 |     21.6 |      3.7 |       3.6 |           0.7 |     0.50 |
| n-queens n=7         |      6.6 |    112.6 |     11.9 |      11.8 |           3.1 |     0.48 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.20 |
| temperature 16384    |      0.0 |      1.8 |      0.0 |       0.0 |           0.0 |     1.57 |
| gol step 12x12       |      1.4 |      9.7 |      1.4 |       1.4 |           0.5 |     0.33 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.55 ms ONCE, run = 0.468 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.468 ms (vs the compiled-in literal, recompiled per grid: 1.01 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.59 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.67 |
| datalog tc n=80        |      6.9 |        — |      4.6 |       4.5 |           4.5 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.04 |       8 |      0.01 |       4 |     0.32 |      0.38 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.25 |
| n-queens n=6         |      0.12 |     0.45 |     184 |      0.18 |     200 |     0.81 |      1.54 |
| n-queens n=7         |      0.11 |     0.54 |     215 |      0.21 |     234 |     0.92 |      4.06 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.25 |     0.02 |       0 |      0.01 |       1 |     0.28 |      0.28 |
| gol step 12x12       |      0.12 |     0.28 |     102 |      0.11 |     221 |     0.57 |      1.04 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.25 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      4.56 |

**comp+run geomean = 0.484 ms ; run-only geomean = 0.099 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-28)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.06 |      2.15 |      1.46 |    1.5x |      1.45 |   1.0x |
| n-queens n=7       |     6.47 |      5.77 |      3.12 |    1.8x |      3.13 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     4.67 |      4.64 |      4.62 |    1.0x |      4.61 |   1.0x |
| sliding 3x3 step   |     0.84 |      0.22 |      0.05 |    4.3x |      0.17 |   3.2x |
| gol step 12x12     |     1.40 |      1.24 |      0.47 |    2.7x |      0.47 |   1.0x |

## Pipeline-stage ablation (2026-06-28)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.032 |    0.008 |    0.059 |    0.076 |    0.072 |
| datalog tc (n=15)  |    0.846 |    0.217 |    0.013 |    0.140 |    0.028 |
| gol step (glider)  |    0.489 |    1.675 |    1.204 |    0.680 |    0.532 |
| sliding 3x3 step   |    3.502 |    1.661 |    0.046 |    2.453 |    0.719 |
| n-queens n=6       |   23.437 |    3.106 |    1.380 |    2.314 |    2.966 |
| temperature 1024   |    0.098 |    0.033 |    0.032 |    0.071 |    0.046 |

## Loop-invariant subgraph hoisting — A/B (2026-06-29)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.06 |    1.8x |     2 |     1 |
| sliding expandStep 3x3 |      0.18 |      0.05 |    3.4x |    17 |    17 |
| n-queens place(6)      |      0.72 |      0.71 |    1.0x |     7 |     7 |

## Benchmark run (2026-06-29)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.3 |       0.5 |       0.2 |     5.7x |    2.2x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.8 |       2.5 |       0.4 |    34.1x |    6.5x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     161.3 |      15.2 |       1.9 |    84.2x |    7.9x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2242.6 |     103.3 |      13.8 |   162.8x |    7.5x |  |
| aunt-query       | family n=150         |      14.5 |       0.9 |       0.1 |   156.9x |   10.0x |  |
| aunt-query       | family n=400         |      95.1 |       5.3 |       0.3 |   377.1x |   21.0x |  |
| aunt-query       | family n=800         |     414.8 |      20.7 |       0.7 |   569.9x |   28.4x |  |
| aunt-query       | family n=1600        |    1795.6 |      78.5 |       1.2 |  1543.6x |   67.5x |  |
| game-of-life     | 16x16 2 steps (68 live) |      24.8 |       5.7 |       3.6 |     6.9x |    1.6x |  |
| game-of-life     | 24x24 2 steps (193 live) |     106.1 |      14.6 |       8.7 |    12.2x |    1.7x |  |
| game-of-life     | 32x32 2 steps (321 live) |     286.3 |      26.2 |      16.1 |    17.8x |    1.6x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   453.5x |    3.2x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1968.1x |    4.2x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  6637.0x |    4.8x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      22.6 |      10.1 |       6.9 |     3.3x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     113.5 |      39.5 |      26.9 |     4.2x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.4 |       2.9 |       1.5 |    14.6x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     127.6 |      12.6 |       6.5 |    19.7x |    1.9x |  |
| n-queens         | n=8 (92 sols, pure)  |     732.7 |      56.9 |      28.3 |    25.9x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     2.3x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.1x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 70.4x vs the
reference Set, and 4.4x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-06-29)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     12.8 |      0.1 |       0.1 |           0.1 |     0.75 |
| aunt n=400           |      0.3 |     85.8 |      0.3 |       0.2 |           0.2 |     0.78 |
| n-queens n=6         |      1.6 |     21.0 |     15.0 |       3.3 |           0.7 |     0.46 |
| n-queens n=7         |      6.6 |    108.8 |     10.7 |      10.5 |           3.1 |     0.47 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.33 |
| temperature 16384    |      0.0 |      1.8 |      0.0 |       0.0 |           0.0 |     2.00 |
| gol step 12x12       |      1.4 |     21.3 |      1.4 |       1.4 |           0.5 |     0.35 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.51 ms ONCE, run = 0.495 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.495 ms (vs the compiled-in literal, recompiled per grid: 1.01 ms each).

| union_iter           |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     0.53 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.65 |
| datalog tc n=80        |      5.6 |        — |      3.6 |       3.7 |           3.7 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.28 |      0.35 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.11 |     0.44 |     184 |      0.17 |     200 |     0.78 |      1.51 |
| n-queens n=7         |      0.10 |     0.52 |     215 |      0.21 |     234 |     0.88 |      3.94 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.08 |      0.08 |
| temperature 16384    |      0.22 |     0.01 |       0 |      0.00 |       1 |     0.25 |      0.25 |
| gol step 12x12       |      0.09 |     0.27 |     102 |      0.11 |     221 |     0.53 |      1.02 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.21 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      3.72 |

**comp+run geomean = 0.450 ms ; run-only geomean = 0.095 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-06-29)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.31 |      2.30 |      1.49 |    1.5x |      1.49 |   1.0x |
| n-queens n=7       |     6.55 |      5.98 |      3.06 |    2.0x |      3.07 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     3.86 |      3.71 |      3.76 |    1.0x |      3.70 |   1.0x |
| sliding 3x3 step   |     0.85 |      0.23 |      0.05 |    4.5x |      0.16 |   3.3x |
| gol step 12x12     |     1.45 |      1.32 |      0.48 |    2.7x |      0.48 |   1.0x |

## Pipeline-stage ablation (2026-06-29)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.033 |    0.008 |    0.058 |    0.081 |    0.075 |
| datalog tc (n=15)  |    0.856 |    0.203 |    0.013 |    0.128 |    0.030 |
| gol step (glider)  |    0.486 |    1.673 |    1.196 |    0.661 |    0.528 |
| sliding 3x3 step   |    3.631 |    1.716 |    0.049 |    2.373 |    0.665 |
| n-queens n=6       |   22.988 |    3.138 |    1.443 |    2.277 |    2.888 |
| temperature 1024   |    0.102 |    0.032 |    0.032 |    0.071 |    0.046 |

## Loop-invariant subgraph hoisting — A/B (2026-07-02)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.11 |      0.06 |    1.9x |     2 |     1 |
| sliding expandStep 3x3 |      0.18 |      0.06 |    3.3x |    17 |    17 |
| n-queens place(6)      |      0.76 |      0.74 |    1.0x |     7 |     7 |

## Benchmark run (2026-07-02)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.2 |       0.5 |       0.1 |    12.9x |    4.8x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.5 |       2.4 |       0.4 |    32.7x |    6.2x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     159.2 |      15.5 |       1.9 |    81.8x |    8.0x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2251.3 |     109.2 |      13.8 |   163.0x |    7.9x |  |
| aunt-query       | family n=150         |      14.9 |       0.9 |       0.1 |   164.7x |    9.7x |  |
| aunt-query       | family n=400         |      96.6 |       5.2 |       0.2 |   389.1x |   20.8x |  |
| aunt-query       | family n=800         |     414.2 |      20.9 |       0.7 |   600.4x |   30.2x |  |
| aunt-query       | family n=1600        |    1770.3 |      77.8 |       1.2 |  1497.5x |   65.8x |  |
| game-of-life     | 16x16 2 steps (68 live) |      26.6 |       8.2 |       5.6 |     4.8x |    1.5x |  |
| game-of-life     | 24x24 2 steps (193 live) |     103.6 |      14.2 |       8.8 |    11.8x |    1.6x |  |
| game-of-life     | 32x32 2 steps (321 live) |     277.5 |      25.7 |      15.8 |    17.5x |    1.6x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   342.3x |    2.7x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1588.7x |    3.2x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  6641.2x |    3.5x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      22.1 |       9.7 |       6.6 |     3.4x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     112.0 |      37.3 |      25.8 |     4.3x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.0 |       2.8 |       1.5 |    15.0x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     122.9 |      12.3 |       6.3 |    19.4x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     702.6 |      54.5 |      27.5 |    25.6x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     0.9x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 70.4x vs the
reference Set, and 4.4x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-07-02)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     13.1 |      0.1 |       0.1 |           0.1 |     0.76 |
| aunt n=400           |      0.2 |     94.4 |      0.3 |       0.2 |           0.2 |     0.82 |
| n-queens n=6         |      1.5 |     21.7 |      3.3 |       3.3 |           0.7 |     0.48 |
| n-queens n=7         |      6.4 |    110.8 |     10.3 |      10.2 |           2.9 |     0.46 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.17 |
| temperature 16384    |      0.0 |      1.8 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.4 |      9.3 |      1.4 |       1.4 |           0.5 |     0.33 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.53 ms ONCE, run = 0.469 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.469 ms (vs the compiled-in literal, recompiled per grid: 1.00 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.59 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.68 |
| datalog tc n=80        |      5.6 |        — |      3.7 |       3.7 |           3.7 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.29 |      0.36 |
| aunt n=400           |      0.00 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.25 |
| n-queens n=6         |      0.22 |     0.43 |     184 |      0.19 |     200 |     0.90 |      1.61 |
| n-queens n=7         |      0.09 |     0.53 |     215 |      0.21 |     234 |     0.90 |      3.85 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.23 |     0.01 |       0 |      0.00 |       1 |     0.25 |      0.25 |
| gol step 12x12       |      0.08 |     0.27 |     102 |      0.10 |     221 |     0.52 |      0.99 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.03 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.21 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      3.69 |

**comp+run geomean = 0.446 ms ; run-only geomean = 0.094 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-07-02)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.04 |      2.11 |      1.38 |    1.5x |      1.38 |   1.0x |
| n-queens n=7       |     6.21 |      5.57 |      2.97 |    1.9x |      3.06 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     3.83 |      3.64 |      3.67 |    1.0x |      3.69 |   1.0x |
| sliding 3x3 step   |     0.82 |      0.23 |      0.05 |    4.4x |      0.17 |   3.3x |
| gol step 12x12     |     1.43 |      1.23 |      0.47 |    2.6x |      0.47 |   1.0x |

## Pipeline-stage ablation (2026-07-02)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.031 |    0.008 |    0.058 |    0.075 |    0.071 |
| datalog tc (n=15)  |    0.853 |    0.198 |    0.014 |    0.128 |    0.028 |
| gol step (glider)  |    0.482 |    1.659 |    1.195 |    0.620 |    0.508 |
| sliding 3x3 step   |    3.639 |    1.696 |    0.049 |    2.326 |    0.636 |
| n-queens n=6       |   23.460 |    3.074 |    1.437 |    2.305 |    2.932 |
| temperature 1024   |    0.107 |    0.031 |    0.031 |    0.069 |    0.044 |

## Loop-invariant subgraph hoisting — A/B (2026-07-02)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.05 |    1.8x |     2 |     1 |
| sliding expandStep 3x3 |      0.17 |      0.05 |    3.4x |    17 |    17 |
| n-queens place(6)      |      0.72 |      0.72 |    1.0x |     7 |     7 |

## Benchmark run (2026-07-02)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.5 |       0.4 |       0.1 |    15.8x |    4.6x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      17.0 |       2.5 |       0.4 |    42.1x |    6.1x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     210.4 |      15.5 |       2.1 |   101.9x |    7.5x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    3293.2 |     102.2 |      14.6 |   225.3x |    7.0x |  |
| aunt-query       | family n=150         |      13.9 |       0.9 |       0.1 |   151.3x |    9.5x |  |
| aunt-query       | family n=400         |      90.6 |       5.2 |       0.3 |   360.7x |   20.6x |  |
| aunt-query       | family n=800         |     407.8 |      20.2 |       0.7 |   589.4x |   29.3x |  |
| aunt-query       | family n=1600        |    1745.1 |      78.7 |       1.2 |  1502.7x |   67.7x |  |
| game-of-life     | 16x16 2 steps (68 live) |      23.9 |       6.4 |       3.7 |     6.5x |    1.7x |  |
| game-of-life     | 24x24 2 steps (193 live) |     102.1 |      15.0 |       8.6 |    11.9x |    1.7x |  |
| game-of-life     | 32x32 2 steps (321 live) |     267.3 |      27.0 |      15.5 |    17.3x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   440.2x |    3.6x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1875.8x |    5.2x |  |
| temperature      | 16384 cells (resident) |       1.6 |       0.0 |       0.0 |  5432.8x |    4.0x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.6 |      10.2 |       6.8 |     3.5x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     116.6 |      38.5 |      27.3 |     4.3x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      21.7 |       2.9 |       1.5 |    14.5x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     122.2 |      12.9 |       6.4 |    19.2x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     708.1 |      57.7 |      27.9 |    25.4x |    2.1x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     0.9x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     0.9x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 75.4x vs the
reference Set, and 4.6x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-07-02)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     16.6 |      0.1 |       0.1 |           0.1 |     0.71 |
| aunt n=400           |      0.3 |     80.1 |      0.3 |       0.2 |           0.2 |     0.78 |
| n-queens n=6         |      1.5 |     20.0 |     15.1 |       3.3 |           0.7 |     0.46 |
| n-queens n=7         |      6.5 |    102.4 |     10.7 |      10.6 |           3.0 |     0.46 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     1.83 |
| temperature 16384    |      0.0 |      1.6 |      0.0 |       0.0 |           0.0 |     2.00 |
| gol step 12x12       |      1.4 |      8.5 |      1.4 |       1.4 |           0.5 |     0.34 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.57 ms ONCE, run = 0.476 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.476 ms (vs the compiled-in literal, recompiled per grid: 1.05 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.49 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.66 |
| datalog tc n=80        |      5.8 |        — |      3.8 |       3.9 |           3.9 |     0.68 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.02 |     0.08 |       8 |      0.03 |       4 |     0.86 |      0.96 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.02 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.11 |     0.43 |     184 |      0.19 |     200 |     0.80 |      1.51 |
| n-queens n=7         |      0.10 |     0.55 |     215 |      0.22 |     234 |     0.92 |      3.93 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.25 |     0.02 |       0 |      0.01 |       1 |     0.29 |      0.29 |
| gol step 12x12       |      0.08 |     0.27 |     102 |      0.11 |     221 |     0.52 |      1.00 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.22 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      3.94 |

**comp+run geomean = 0.512 ms ; run-only geomean = 0.098 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-07-02)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.20 |      2.20 |      1.48 |    1.5x |      1.47 |   1.0x |
| n-queens n=7       |     6.37 |      5.58 |      2.99 |    1.9x |      3.00 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     3.97 |      3.95 |      3.87 |    1.0x |      3.87 |   1.0x |
| sliding 3x3 step   |     0.84 |      0.22 |      0.05 |    4.5x |      0.16 |   3.3x |
| gol step 12x12     |     1.40 |      1.24 |      0.47 |    2.6x |      0.47 |   1.0x |

## Pipeline-stage ablation (2026-07-02)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.029 |    0.008 |    0.059 |    0.081 |    0.072 |
| datalog tc (n=15)  |    0.814 |    0.208 |    0.015 |    0.135 |    0.030 |
| gol step (glider)  |    0.458 |    1.688 |    1.215 |    0.648 |    0.545 |
| sliding 3x3 step   |    3.598 |    1.681 |    0.050 |    2.403 |    0.690 |
| n-queens n=6       |   22.358 |    2.978 |    1.392 |    2.239 |    2.838 |
| temperature 1024   |    0.097 |    0.034 |    0.033 |    0.071 |    0.046 |

## Loop-invariant subgraph hoisting — A/B (2026-07-02)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.06 |    1.8x |     2 |     1 |
| sliding expandStep 3x3 |      0.19 |      0.05 |    3.5x |    17 |    17 |
| n-queens place(6)      |      0.79 |      0.79 |    1.0x |     7 |     7 |

## Benchmark run (2026-07-02)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.2 |       1.1 |       0.1 |    11.4x |   10.0x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.5 |       2.3 |       0.5 |    26.7x |    4.9x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     155.0 |      14.5 |       2.6 |    60.3x |    5.7x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2172.2 |      96.4 |      18.4 |   118.3x |    5.2x |  |
| aunt-query       | family n=150         |      14.2 |       0.8 |       0.1 |   157.5x |    9.3x |  |
| aunt-query       | family n=400         |      91.7 |       5.1 |       0.2 |   380.7x |   21.3x |  |
| aunt-query       | family n=800         |     402.4 |      20.0 |       0.7 |   587.1x |   29.2x |  |
| aunt-query       | family n=1600        |    1746.4 |      74.1 |       1.1 |  1547.6x |   65.7x |  |
| game-of-life     | 16x16 2 steps (68 live) |      23.5 |       5.9 |       3.7 |     6.4x |    1.6x |  |
| game-of-life     | 24x24 2 steps (193 live) |     102.2 |      15.0 |       8.6 |    11.9x |    1.8x |  |
| game-of-life     | 32x32 2 steps (321 live) |     273.4 |      27.1 |      15.6 |    17.5x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   390.0x |    3.6x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1465.0x |    3.7x |  |
| temperature      | 16384 cells (resident) |       1.6 |       0.0 |       0.0 |  6206.0x |    3.8x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.3 |      10.1 |       7.1 |     3.3x |    1.4x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     113.4 |      39.0 |      26.5 |     4.3x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.0 |       2.9 |       1.5 |    14.3x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     120.8 |      12.8 |       6.7 |    18.1x |    1.9x |  |
| n-queens         | n=8 (92 sols, pure)  |     700.3 |      57.8 |      29.5 |    23.7x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     0.8x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.3x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 66.9x vs the
reference Set, and 4.4x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-07-02)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     15.5 |      0.1 |       0.1 |           0.1 |     0.72 |
| aunt n=400           |      0.2 |     95.2 |      0.3 |       0.2 |           0.2 |     0.89 |
| n-queens n=6         |      1.5 |     21.4 |      3.4 |       3.4 |           0.8 |     0.51 |
| n-queens n=7         |      6.5 |    109.5 |     11.1 |      11.0 |           3.3 |     0.51 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.33 |
| temperature 16384    |      0.0 |      1.8 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.4 |      9.4 |      1.5 |       1.4 |           0.5 |     0.36 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.51 ms ONCE, run = 0.502 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.502 ms (vs the compiled-in literal, recompiled per grid: 1.01 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.60 |
| datalog tc n=40        |      0.4 |        — |      0.2 |       0.2 |           0.2 |     0.68 |
| datalog tc n=80        |      7.6 |        — |      5.0 |       5.0 |           5.0 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.04 |       8 |      0.02 |       4 |     0.40 |      0.49 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.10 |     0.43 |     184 |      0.17 |     200 |     0.76 |      1.55 |
| n-queens n=7         |      0.09 |     0.51 |     215 |      0.21 |     234 |     0.87 |      4.18 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.26 |     0.02 |       0 |      0.01 |       1 |     0.30 |      0.30 |
| gol step 12x12       |      0.08 |     0.27 |     102 |      0.11 |     221 |     0.51 |      1.01 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.26 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      5.02 |

**comp+run geomean = 0.505 ms ; run-only geomean = 0.106 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-07-02)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.6x |      0.00 |   1.0x |
| aunt (royal92)     |     2.09 |      2.36 |      1.51 |    1.6x |      1.50 |   1.0x |
| n-queens n=7       |     6.52 |      6.16 |      3.30 |    1.9x |      3.32 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     5.07 |      4.98 |      4.98 |    1.0x |      4.97 |   1.0x |
| sliding 3x3 step   |     0.85 |      0.24 |      0.05 |    4.5x |      0.17 |   3.3x |
| gol step 12x12     |     1.41 |      1.34 |      0.49 |    2.7x |      0.50 |   1.0x |

## Pipeline-stage ablation (2026-07-02)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.031 |    0.008 |    0.058 |    0.076 |    0.071 |
| datalog tc (n=15)  |    0.834 |    0.223 |    0.014 |    0.154 |    0.028 |
| gol step (glider)  |    0.456 |    1.626 |    1.196 |    0.645 |    0.511 |
| sliding 3x3 step   |    3.550 |    1.705 |    0.048 |    2.659 |    0.723 |
| n-queens n=6       |   23.420 |    3.190 |    1.426 |    2.449 |    3.058 |
| temperature 1024   |    0.092 |    0.032 |    0.031 |    0.069 |    0.043 |

## Loop-invariant subgraph hoisting — A/B (2026-07-03)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.8x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.05 |    1.9x |     2 |     1 |
| sliding expandStep 3x3 |      0.17 |      0.05 |    3.3x |    17 |    17 |
| n-queens place(6)      |      0.73 |      0.73 |    1.0x |     7 |     7 |

## Benchmark run (2026-07-03)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.3 |       0.5 |       0.2 |     6.0x |    2.1x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      13.9 |       2.3 |       0.4 |    36.7x |    6.0x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     180.5 |      14.4 |       1.9 |    92.8x |    7.4x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2630.6 |      99.7 |      13.3 |   198.3x |    7.5x |  |
| aunt-query       | family n=150         |      15.2 |       0.8 |       0.1 |   157.7x |    8.7x |  |
| aunt-query       | family n=400         |     103.2 |       5.2 |       0.3 |   400.8x |   20.4x |  |
| aunt-query       | family n=800         |     441.3 |      19.7 |       0.7 |   626.8x |   27.9x |  |
| aunt-query       | family n=1600        |    1845.7 |      78.4 |       1.2 |  1563.5x |   66.4x |  |
| game-of-life     | 16x16 2 steps (68 live) |      26.7 |       5.6 |       3.7 |     7.2x |    1.5x |  |
| game-of-life     | 24x24 2 steps (193 live) |     114.5 |      14.0 |       9.3 |    12.4x |    1.5x |  |
| game-of-life     | 32x32 2 steps (321 live) |     297.1 |      25.5 |      15.8 |    18.8x |    1.6x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   474.6x |    3.6x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1665.0x |    3.3x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  6715.8x |    3.8x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.9 |       9.9 |       6.9 |     3.5x |    1.4x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     114.8 |      37.8 |      26.5 |     4.3x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      23.2 |       2.7 |       1.5 |    15.1x |    1.8x |  |
| n-queens         | n=7 (40 sols, pure)  |     128.7 |      12.1 |       6.6 |    19.6x |    1.8x |  |
| n-queens         | n=8 (92 sols, pure)  |     748.8 |      54.3 |      29.0 |    25.8x |    1.9x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.1x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 73.0x vs the
reference Set, and 4.1x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-07-03)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     15.9 |      0.1 |       0.1 |           0.1 |     0.82 |
| aunt n=400           |      0.2 |    100.9 |      0.3 |       0.2 |           0.2 |     0.80 |
| n-queens n=6         |      1.5 |     22.3 |      3.3 |       3.3 |           0.7 |     0.47 |
| n-queens n=7         |      6.5 |    113.8 |     10.9 |      10.8 |           3.2 |     0.49 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.20 |
| temperature 16384    |      0.0 |      1.9 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.4 |     11.4 |      1.4 |       1.4 |           0.5 |     0.34 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.52 ms ONCE, run = 0.497 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.497 ms (vs the compiled-in literal, recompiled per grid: 1.02 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.56 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.66 |
| datalog tc n=80        |      5.9 |        — |      3.7 |       3.9 |           3.9 |     0.67 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.04 |       8 |      0.02 |       4 |     0.39 |      0.48 |
| aunt n=400           |      0.01 |     0.04 |       8 |      0.01 |       4 |     0.07 |      0.26 |
| n-queens n=6         |      0.10 |     0.43 |     184 |      0.16 |     200 |     0.74 |      1.45 |
| n-queens n=7         |      0.09 |     0.53 |     215 |      0.22 |     234 |     0.90 |      4.06 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.24 |     0.01 |       0 |      0.00 |       1 |     0.27 |      0.27 |
| gol step 12x12       |      0.08 |     0.28 |     102 |      0.10 |     221 |     0.53 |      1.02 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.04 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.21 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      3.94 |

**comp+run geomean = 0.479 ms ; run-only geomean = 0.099 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-07-03)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.0x |
| aunt (royal92)     |     2.09 |      2.12 |      1.42 |    1.5x |      1.41 |   1.0x |
| n-queens n=7       |     6.38 |      5.77 |      3.01 |    1.9x |      3.09 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     3.64 |      3.61 |      3.63 |    1.0x |      3.59 |   1.0x |
| sliding 3x3 step   |     0.87 |      0.22 |      0.05 |    4.3x |      0.16 |   3.3x |
| gol step 12x12     |     1.47 |      1.27 |      0.49 |    2.6x |      0.48 |   1.0x |

## Pipeline-stage ablation (2026-07-03)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.033 |    0.008 |    0.060 |    0.077 |    0.070 |
| datalog tc (n=15)  |    0.891 |    0.207 |    0.014 |    0.129 |    0.029 |
| gol step (glider)  |    0.506 |    1.683 |    1.191 |    0.623 |    0.502 |
| sliding 3x3 step   |    3.667 |    1.731 |    0.050 |    2.239 |    0.639 |
| n-queens n=6       |   23.495 |    3.036 |    1.431 |    2.255 |    2.828 |
| temperature 1024   |    0.109 |    0.031 |    0.032 |    0.071 |    0.044 |

## Loop-invariant subgraph hoisting — A/B (2026-07-04)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    2.0x |     2 |     1 |
| invariant-inner N=400  |      0.10 |      0.06 |    1.9x |     2 |     1 |
| sliding expandStep 3x3 |      0.18 |      0.06 |    3.3x |    17 |    17 |
| n-queens place(6)      |      0.76 |      0.77 |    1.0x |     7 |     7 |

## Benchmark run (2026-07-04)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.2 |       0.5 |       0.1 |    11.9x |    4.6x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      12.6 |       2.3 |       0.4 |    32.6x |    6.0x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     162.5 |      14.6 |       2.0 |    83.3x |    7.5x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2235.4 |      98.6 |      13.8 |   162.2x |    7.2x |  |
| aunt-query       | family n=150         |      12.3 |       0.9 |       0.1 |   137.6x |    9.7x |  |
| aunt-query       | family n=400         |      87.7 |       5.3 |       0.3 |   348.8x |   21.0x |  |
| aunt-query       | family n=800         |     381.5 |      20.4 |       0.7 |   549.0x |   29.4x |  |
| aunt-query       | family n=1600        |    1664.0 |      79.2 |       1.2 |  1418.3x |   67.5x |  |
| game-of-life     | 16x16 2 steps (68 live) |      23.6 |       5.7 |       3.6 |     6.6x |    1.6x |  |
| game-of-life     | 24x24 2 steps (193 live) |     100.5 |      14.3 |       8.6 |    11.7x |    1.7x |  |
| game-of-life     | 32x32 2 steps (321 live) |     265.1 |      26.1 |      15.0 |    17.6x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   427.8x |    3.6x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1613.8x |    3.2x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  6656.0x |    5.0x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.2 |      10.4 |       7.3 |     3.2x |    1.4x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     114.9 |      38.5 |      26.5 |     4.3x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.3 |       2.8 |       1.5 |    15.2x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     120.6 |      12.5 |       6.3 |    19.1x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     697.6 |      56.7 |      28.3 |    24.7x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.1x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.2x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 70.2x vs the
reference Set, and 4.5x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-07-04)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     11.0 |      0.1 |       0.1 |           0.1 |     0.72 |
| aunt n=400           |      0.3 |     79.1 |      0.3 |       0.2 |           0.2 |     0.75 |
| n-queens n=6         |      1.6 |     20.9 |      3.5 |       3.4 |           0.7 |     0.46 |
| n-queens n=7         |      6.7 |    102.8 |     10.5 |      10.4 |           2.9 |     0.44 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     1.67 |
| temperature 16384    |      0.0 |      2.0 |      0.0 |       0.0 |           0.0 |     1.50 |
| gol step 12x12       |      1.4 |      8.3 |      1.4 |       1.4 |           0.5 |     0.32 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.47 ms ONCE, run = 0.467 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.467 ms (vs the compiled-in literal, recompiled per grid: 0.94 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.46 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.66 |
| datalog tc n=80        |      5.6 |        — |      3.7 |       3.7 |           3.7 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.04 |       8 |      0.01 |       4 |     0.28 |      0.35 |
| aunt n=400           |      0.00 |     0.03 |       8 |      0.01 |       4 |     0.05 |      0.25 |
| n-queens n=6         |      0.23 |     0.43 |     184 |      0.17 |     200 |     0.89 |      1.61 |
| n-queens n=7         |      0.09 |     0.50 |     215 |      0.21 |     234 |     0.87 |      3.81 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.08 |      0.08 |
| temperature 16384    |      0.22 |     0.01 |       0 |      0.01 |       1 |     0.24 |      0.24 |
| gol step 12x12       |      0.08 |     0.25 |     102 |      0.10 |     221 |     0.49 |      0.96 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.21 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      3.76 |

**comp+run geomean = 0.445 ms ; run-only geomean = 0.094 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-07-04)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.7x |      0.00 |   1.0x |
| aunt (royal92)     |     2.17 |      2.13 |      1.44 |    1.5x |      1.43 |   1.0x |
| n-queens n=7       |     6.64 |      5.69 |      2.97 |    1.9x |      2.98 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     3.85 |      3.74 |      3.73 |    1.0x |      3.74 |   1.0x |
| sliding 3x3 step   |     0.88 |      0.22 |      0.05 |    4.4x |      0.17 |   3.3x |
| gol step 12x12     |     1.42 |      1.25 |      0.47 |    2.7x |      0.47 |   1.0x |

## Pipeline-stage ablation (2026-07-04)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.029 |    0.008 |    0.060 |    0.073 |    0.069 |
| datalog tc (n=15)  |    0.811 |    0.203 |    0.013 |    0.128 |    0.027 |
| gol step (glider)  |    0.470 |    1.633 |    1.200 |    0.627 |    0.522 |
| sliding 3x3 step   |    3.679 |    1.770 |    0.053 |    2.276 |    0.619 |
| n-queens n=6       |   21.826 |    3.102 |    1.438 |    2.210 |    2.721 |
| temperature 1024   |    0.100 |    0.032 |    0.032 |    0.068 |    0.043 |

## Loop-invariant subgraph hoisting — A/B (2026-07-04)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.8x |     2 |     1 |
| invariant-inner N=400  |      0.11 |      0.05 |    1.9x |     2 |     1 |
| sliding expandStep 3x3 |      0.21 |      0.06 |    3.6x |    17 |    17 |
| n-queens place(6)      |      0.76 |      0.76 |    1.0x |     7 |     7 |

## Benchmark run (2026-07-04)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.2 |       0.5 |       0.3 |     4.9x |    1.9x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      13.0 |       2.3 |       0.3 |    37.3x |    6.7x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     161.7 |      15.0 |       2.0 |    82.9x |    7.7x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    2242.6 |     101.4 |      13.8 |   162.5x |    7.3x |  |
| aunt-query       | family n=150         |      12.2 |       0.9 |       0.1 |   138.8x |   10.0x |  |
| aunt-query       | family n=400         |      91.5 |       5.2 |       0.3 |   358.6x |   20.5x |  |
| aunt-query       | family n=800         |     378.6 |      20.5 |       0.7 |   536.4x |   29.1x |  |
| aunt-query       | family n=1600        |    1703.3 |      77.9 |       1.2 |  1473.4x |   67.4x |  |
| game-of-life     | 16x16 2 steps (68 live) |      23.6 |       5.9 |       3.9 |     6.1x |    1.5x |  |
| game-of-life     | 24x24 2 steps (193 live) |     102.4 |      14.7 |       8.9 |    11.5x |    1.6x |  |
| game-of-life     | 32x32 2 steps (321 live) |     267.7 |      26.7 |      15.4 |    17.3x |    1.7x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   419.4x |    3.5x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1522.7x |    3.2x |  |
| temperature      | 16384 cells (resident) |       1.6 |       0.0 |       0.0 |  7420.7x |    6.2x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      23.2 |      10.5 |       6.9 |     3.4x |    1.5x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     114.1 |      38.3 |      27.2 |     4.2x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      21.6 |       2.8 |       1.5 |    14.7x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     122.7 |      12.8 |       6.4 |    19.1x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     691.2 |      56.7 |      28.2 |    24.5x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     1.2x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.0x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.3x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 67.3x vs the
reference Set, and 4.4x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-07-04)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     14.0 |      0.1 |       0.1 |           0.1 |     0.77 |
| aunt n=400           |      0.2 |     95.0 |      0.3 |       0.2 |           0.2 |     0.78 |
| n-queens n=6         |      1.5 |     21.5 |      3.3 |       3.2 |           0.7 |     0.48 |
| n-queens n=7         |      6.4 |    108.9 |     10.2 |      10.1 |           3.0 |     0.47 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     2.17 |
| temperature 16384    |      0.0 |      1.7 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.4 |     10.8 |      1.4 |       1.4 |           0.5 |     0.34 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.48 ms ONCE, run = 0.479 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.479 ms (vs the compiled-in literal, recompiled per grid: 0.96 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.52 |
| datalog tc n=40        |      0.3 |        — |      0.2 |       0.2 |           0.2 |     0.66 |
| datalog tc n=80        |      5.6 |        — |      3.7 |       3.7 |           3.7 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.04 |       8 |      0.01 |       4 |     0.66 |      0.73 |
| aunt n=400           |      0.00 |     0.03 |       8 |      0.01 |       4 |     0.05 |      0.25 |
| n-queens n=6         |      0.10 |     0.43 |     184 |      0.17 |     200 |     0.75 |      1.46 |
| n-queens n=7         |      0.09 |     0.52 |     215 |      0.21 |     234 |     0.88 |      3.89 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.08 |      0.08 |
| temperature 16384    |      0.22 |     0.01 |       0 |      0.01 |       1 |     0.25 |      0.25 |
| gol step 12x12       |      0.07 |     0.27 |     102 |      0.10 |     221 |     0.50 |      0.99 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.03 |      0.04 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.20 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      3.69 |

**comp+run geomean = 0.470 ms ; run-only geomean = 0.094 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-07-04)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.5x |      0.00 |   1.1x |
| aunt (royal92)     |     2.16 |      2.20 |      1.47 |    1.5x |      1.47 |   1.0x |
| n-queens n=7       |     6.40 |      5.79 |      3.01 |    1.9x |      2.99 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.5x |
| datalog tc (n=80)  |     3.96 |      3.71 |      3.69 |    1.0x |      3.68 |   1.0x |
| sliding 3x3 step   |     0.88 |      0.22 |      0.05 |    4.4x |      0.16 |   3.3x |
| gol step 12x12     |     1.44 |      1.25 |      0.48 |    2.6x |      0.48 |   1.0x |

## Pipeline-stage ablation (2026-07-04)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.031 |    0.008 |    0.060 |    0.076 |    0.072 |
| datalog tc (n=15)  |    0.834 |    0.202 |    0.014 |    0.126 |    0.028 |
| gol step (glider)  |    0.466 |    1.649 |    1.190 |    0.632 |    0.514 |
| sliding 3x3 step   |    3.629 |    1.763 |    0.049 |    2.337 |    0.668 |
| n-queens n=6       |   22.891 |    2.960 |    1.425 |    2.247 |    2.816 |
| temperature 1024   |    0.098 |    0.035 |    0.034 |    0.072 |    0.046 |

## Loop-invariant subgraph hoisting — A/B (2026-07-06)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.04 |      0.02 |    1.9x |     2 |     1 |
| invariant-inner N=400  |      0.11 |      0.06 |    1.9x |     2 |     1 |
| sliding expandStep 3x3 |      0.18 |      0.05 |    3.7x |    17 |    17 |
| n-queens place(6)      |      0.79 |      0.81 |    1.0x |     7 |     7 |

## Benchmark run (2026-07-06)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       1.5 |       0.4 |       0.2 |     6.4x |    1.5x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      17.0 |       1.9 |       0.5 |    37.1x |    4.2x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     209.6 |      11.6 |       2.5 |    84.8x |    4.7x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    3284.5 |      80.5 |      18.2 |   180.3x |    4.4x |  |
| aunt-query       | family n=150         |      13.9 |       0.5 |       0.1 |   156.3x |    5.2x |  |
| aunt-query       | family n=400         |      95.7 |       3.2 |       0.3 |   365.2x |   12.3x |  |
| aunt-query       | family n=800         |     404.8 |      14.4 |       0.8 |   524.9x |   18.6x |  |
| aunt-query       | family n=1600        |    1866.7 |      59.7 |       1.3 |  1397.4x |   44.7x |  |
| game-of-life     | 16x16 2 steps (68 live) |      23.8 |       5.1 |       3.9 |     6.2x |    1.3x |  |
| game-of-life     | 24x24 2 steps (193 live) |     103.2 |      13.1 |       8.9 |    11.6x |    1.5x |  |
| game-of-life     | 32x32 2 steps (321 live) |     271.7 |      23.6 |      16.5 |    16.5x |    1.4x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   429.9x |    2.8x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |  1964.1x |    2.4x |  |
| temperature      | 16384 cells (resident) |       1.8 |       0.0 |       0.0 |  7353.3x |    2.3x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      22.2 |       9.1 |       7.3 |     3.0x |    1.3x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     102.5 |      34.5 |      26.7 |     3.8x |    1.3x |  |
| n-queens         | n=6 (4 sols, pure)   |      21.1 |       2.5 |       2.1 |    10.2x |    1.2x |  |
| n-queens         | n=7 (40 sols, pure)  |     115.4 |      11.0 |       6.9 |    16.8x |    1.6x |  |
| n-queens         | n=8 (92 sols, pure)  |     680.2 |      49.2 |      30.2 |    22.5x |    1.6x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     2.1x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     0.9x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.3x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 67.0x vs the
reference Set, and 3.1x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-07-06)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     13.9 |      0.1 |       0.1 |           0.1 |     0.83 |
| aunt n=400           |      0.3 |     81.8 |      0.3 |       0.2 |           0.2 |     0.80 |
| n-queens n=6         |      1.6 |     21.5 |      3.6 |       3.5 |           0.8 |     0.49 |
| n-queens n=7         |      6.9 |    119.2 |     11.4 |      11.2 |           3.6 |     0.52 |
| temperature 4096     |      0.0 |      0.4 |      0.0 |       0.0 |           0.0 |     1.67 |
| temperature 16384    |      0.0 |      2.7 |      0.0 |       0.0 |           0.0 |     1.66 |
| gol step 12x12       |      1.5 |     21.5 |      1.5 |       1.4 |           0.5 |     0.33 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.53 ms ONCE, run = 0.503 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.503 ms (vs the compiled-in literal, recompiled per grid: 1.04 ms each).

| union_iter           |      0.0 |      0.3 |      0.0 |       0.0 |           0.0 |     0.54 |
| datalog tc n=40        |      0.4 |        — |      0.2 |       0.2 |           0.2 |     0.69 |
| datalog tc n=80        |      7.3 |        — |      4.8 |       4.8 |           4.8 |     0.66 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.01 |     0.05 |       8 |      0.01 |       4 |     0.73 |      0.80 |
| aunt n=400           |      0.01 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.11 |     0.44 |     184 |      0.18 |     200 |     0.78 |      1.58 |
| n-queens n=7         |      0.10 |     0.55 |     215 |      0.23 |     234 |     0.95 |      4.51 |
| temperature 4096     |      0.06 |     0.01 |       0 |      0.00 |       1 |     0.09 |      0.09 |
| temperature 16384    |      0.25 |     0.02 |       0 |      0.00 |       1 |     0.28 |      0.28 |
| gol step 12x12       |      0.08 |     0.28 |     102 |      0.11 |     221 |     0.53 |      1.04 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.04 |      0.04 |
| datalog tc n=40        |      0.02 |     0.02 |       0 |      0.00 |       0 |     0.04 |      0.28 |
| datalog tc n=80        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.03 |      4.83 |

**comp+run geomean = 0.544 ms ; run-only geomean = 0.105 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-07-06)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.00 |      0.00 |      0.00 |    1.6x |      0.00 |   1.0x |
| aunt (royal92)     |     2.35 |      2.47 |      1.55 |    1.6x |      1.55 |   1.0x |
| n-queens n=7       |     6.94 |      6.58 |      3.55 |    1.9x |      3.54 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     4.81 |      4.81 |      4.80 |    1.0x |      4.81 |   1.0x |
| sliding 3x3 step   |     1.06 |      0.26 |      0.06 |    4.5x |      0.19 |   3.3x |
| gol step 12x12     |     1.57 |      1.46 |      0.55 |    2.7x |      0.51 |   0.9x |

## Pipeline-stage ablation (2026-07-06)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.028 |    0.008 |    0.059 |    0.075 |    0.072 |
| datalog tc (n=15)  |    0.773 |    0.222 |    0.015 |    0.151 |    0.030 |
| gol step (glider)  |    0.454 |    1.714 |    1.239 |    0.746 |    0.537 |
| sliding 3x3 step   |    3.218 |    1.773 |    0.049 |    2.505 |    0.636 |
| n-queens n=6       |   20.938 |    3.291 |    1.534 |    2.508 |    3.239 |
| temperature 1024   |    0.096 |    0.035 |    0.033 |    0.074 |    0.046 |

## Loop-invariant subgraph hoisting — A/B (2026-07-11)

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.08 |      0.03 |    3.0x |     2 |     1 |
| invariant-inner N=400  |      0.47 |      0.16 |    3.0x |     2 |     1 |
| sliding expandStep 3x3 |      0.36 |      0.12 |    2.9x |    17 |    17 |
| n-queens place(6)      |      1.27 |      1.22 |    1.0x |     7 |     7 |

## Benchmark run (2026-07-11)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       2.1 |       0.9 |       0.1 |    15.5x |    6.3x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      26.6 |       4.4 |       0.4 |    61.9x |   10.3x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     322.9 |      18.5 |       2.0 |   161.2x |    9.2x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    4371.3 |     136.1 |      18.0 |   243.4x |    7.6x |  |
| aunt-query       | family n=150         |      29.1 |       1.1 |       0.1 |   306.2x |   11.3x |  |
| aunt-query       | family n=400         |     173.7 |       3.4 |       0.3 |   681.6x |   13.3x |  |
| aunt-query       | family n=800         |     769.1 |      18.2 |       0.7 |  1107.4x |   26.2x |  |
| aunt-query       | family n=1600        |    3312.4 |      96.3 |       1.2 |  2688.5x |   78.1x |  |
| game-of-life     | 16x16 2 steps (68 live) |      42.8 |      11.7 |       8.5 |     5.0x |    1.4x |  |
| game-of-life     | 24x24 2 steps (193 live) |     198.7 |      21.7 |      11.4 |    17.4x |    1.9x |  |
| game-of-life     | 32x32 2 steps (321 live) |     481.0 |      33.3 |      24.9 |    19.3x |    1.3x |  |
| temperature      | 1024 cells (resident) |       0.2 |       0.0 |       0.0 |   561.9x |    4.7x |  |
| temperature      | 4096 cells (resident) |       1.1 |       0.0 |       0.0 |  2620.4x |    5.9x |  |
| temperature      | 16384 cells (resident) |       1.7 |       0.0 |       0.0 |  3673.1x |    5.2x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      32.4 |      13.8 |      11.7 |     2.8x |    1.2x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     154.6 |      58.1 |      39.6 |     3.9x |    1.5x |  |
| n-queens         | n=6 (4 sols, pure)   |      30.1 |       2.7 |       1.6 |    18.3x |    1.6x |  |
| n-queens         | n=7 (40 sols, pure)  |     191.8 |      17.1 |       9.3 |    20.6x |    1.8x |  |
| n-queens         | n=8 (92 sols, pure)  |    1110.1 |      76.4 |      45.7 |    24.3x |    1.7x |  |
| join-all         | k=200 m=200          |       0.1 |      -1.0 |       0.0 |     3.1x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.0 |      -1.0 |       0.0 |     1.1x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.1 |     0.2x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 92.1x vs the
reference Set, and 4.7x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is created during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Op-graph backend benchmark (2026-07-11)

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.1 |     22.8 |      0.3 |       0.2 |           0.2 |     1.19 |
| aunt n=400           |      0.3 |    145.0 |      0.7 |       0.2 |           0.2 |     0.75 |
| n-queens n=6         |      2.4 |     34.7 |     20.4 |       3.6 |           0.8 |     0.32 |
| n-queens n=7         |      7.9 |    172.0 |     13.2 |      13.3 |           3.4 |     0.43 |
| temperature 4096     |      0.0 |      0.5 |      0.0 |       0.0 |           0.0 |     1.00 |
| temperature 16384    |      0.0 |      2.3 |      0.0 |       0.0 |           0.0 |     1.83 |
| gol step 12x12       |      1.7 |     16.1 |      1.5 |       1.5 |           0.5 |     0.32 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 0.54 ms ONCE, run = 0.537 ms/step.  Amortized comp+run over K steps =
compile/K + run → 0.537 ms (vs the compiled-in literal, recompiled per grid: 1.08 ms each).

| union_iter           |      0.0 |      0.6 |      0.0 |       0.0 |           0.0 |     1.68 |
| datalog tc n=40        |      0.7 |        — |      0.2 |       0.2 |           0.2 |     0.32 |
| datalog tc n=80        |      8.6 |        — |      5.2 |       5.1 |           5.1 |     0.60 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.03 |     0.14 |       8 |      0.04 |       4 |     0.85 |      1.02 |
| aunt n=400           |      0.00 |     0.03 |       8 |      0.01 |       4 |     0.06 |      0.26 |
| n-queens n=6         |      0.28 |     1.01 |     184 |      0.45 |     200 |     1.89 |      2.68 |
| n-queens n=7         |      0.25 |     1.31 |     215 |      0.53 |     234 |     2.22 |      5.61 |
| temperature 4096     |      0.05 |     0.01 |       0 |      0.00 |       1 |     0.07 |      0.07 |
| temperature 16384    |      0.21 |     0.01 |       0 |      0.00 |       1 |     0.24 |      0.24 |
| gol step 12x12       |      0.22 |     0.60 |     102 |      0.24 |     221 |     1.19 |      1.73 |
| union_iter           |      0.00 |     0.02 |       2 |      0.01 |       0 |     0.04 |      0.06 |
| datalog tc n=40        |      0.01 |     0.01 |       0 |      0.00 |       0 |     0.02 |      0.27 |
| datalog tc n=80        |      0.02 |     0.02 |       0 |      0.01 |       0 |     0.04 |      5.16 |

**comp+run geomean = 0.622 ms ; run-only geomean = 0.128 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

## Optimization across all SC domains (2026-07-11)

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.01 |      0.01 |      0.01 |    1.5x |      0.01 |   1.0x |
| aunt (royal92)     |     2.37 |      2.37 |      1.64 |    1.4x |      1.67 |   1.0x |
| n-queens n=7       |     7.27 |      6.31 |      3.40 |    1.9x |      3.39 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    0.5x |      0.00 |   0.4x |
| datalog tc (n=80)  |     5.47 |      5.15 |      5.11 |    1.0x |      5.07 |   1.0x |
| sliding 3x3 step   |     0.91 |      0.24 |      0.05 |    4.4x |      0.18 |   3.4x |
| gol step 12x12     |     1.63 |      1.43 |      0.55 |    2.6x |      0.54 |   1.0x |

## Pipeline-stage ablation (2026-07-11)

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.033 |    0.009 |    0.063 |    0.081 |    0.074 |
| datalog tc (n=15)  |    0.860 |    0.475 |    0.033 |    0.176 |    0.061 |
| gol step (glider)  |    1.242 |    1.802 |    1.619 |    1.556 |    1.179 |
| sliding 3x3 step   |    3.296 |    1.821 |    0.114 |    2.740 |    0.686 |
| n-queens n=6       |   30.366 |    3.314 |    1.668 |    2.515 |    3.252 |
| temperature 1024   |    0.248 |    0.076 |    0.075 |    0.159 |    0.100 |

## Benchmark run (2026-07-12)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       2.7 |       2.6 |       0.7 |     3.6x |    3.5x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      13.6 |       6.3 |       1.2 |    11.4x |    5.3x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     106.0 |      14.9 |       3.2 |    33.3x |    4.7x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    1256.5 |      88.8 |      11.9 |   105.5x |    7.5x |  |
| aunt-query       | family n=150         |      19.0 |       1.1 |       0.3 |    62.1x |    3.5x |  |
| aunt-query       | family n=400         |      64.4 |       5.3 |       0.3 |   204.5x |   16.7x |  |
| aunt-query       | family n=800         |     268.2 |      20.1 |       0.7 |   391.4x |   29.4x |  |
| aunt-query       | family n=1600        |    1349.2 |      80.4 |       1.1 |  1207.8x |   72.0x |  |
| game-of-life     | 16x16 2 steps (68 live) |      30.8 |      16.5 |       8.5 |     3.6x |    1.9x |  |
| game-of-life     | 24x24 2 steps (193 live) |      94.3 |      18.4 |      10.3 |     9.2x |    1.8x |  |
| game-of-life     | 32x32 2 steps (321 live) |     226.5 |      28.2 |      13.5 |    16.8x |    2.1x |  |
| temperature      | 1024 cells (resident) |       0.3 |       0.0 |       0.0 |    62.5x |    2.3x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |    64.6x |    1.5x |  |
| temperature      | 16384 cells (resident) |       1.2 |       0.0 |       0.0 |   905.2x |    1.4x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      46.3 |      17.7 |      18.2 |     2.5x |    1.0x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     109.7 |      35.8 |      25.9 |     4.2x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      22.2 |       4.6 |       2.3 |     9.5x |    1.9x |  |
| n-queens         | n=7 (40 sols, pure)  |     113.0 |      12.5 |       6.1 |    18.5x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     645.1 |      56.0 |      26.3 |    24.5x |    2.1x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     3.7x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.1 |      -1.0 |       0.0 |     2.0x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.1x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.4x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 33.3x vs the
reference Set, and 3.6x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is touched during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


## Benchmark run (2026-07-12)

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       5.1 |       2.8 |       0.6 |     8.1x |    4.4x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      11.3 |       3.4 |       0.9 |    12.8x |    3.9x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     101.6 |      12.7 |       2.0 |    50.7x |    6.3x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    1236.0 |      85.0 |      11.9 |   104.0x |    7.1x |  |
| aunt-query       | family n=150         |       9.3 |       1.2 |       0.3 |    31.1x |    3.9x |  |
| aunt-query       | family n=400         |      64.5 |       5.4 |       0.3 |   207.2x |   17.4x |  |
| aunt-query       | family n=800         |     287.7 |      18.9 |       0.6 |   452.2x |   29.8x |  |
| aunt-query       | family n=1600        |    1351.0 |      77.3 |       1.1 |  1279.1x |   73.2x |  |
| game-of-life     | 16x16 2 steps (68 live) |      23.7 |       7.7 |       5.0 |     4.8x |    1.5x |  |
| game-of-life     | 24x24 2 steps (193 live) |      85.4 |      15.3 |       8.4 |    10.1x |    1.8x |  |
| game-of-life     | 32x32 2 steps (321 live) |     226.8 |      27.5 |      13.8 |    16.4x |    2.0x |  |
| temperature      | 1024 cells (resident) |       0.8 |       0.0 |       0.0 |   177.7x |    1.8x |  |
| temperature      | 4096 cells (resident) |       0.4 |       0.0 |       0.0 |    71.3x |    1.4x |  |
| temperature      | 16384 cells (resident) |       1.1 |       0.0 |       0.0 |   686.9x |    2.0x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      41.5 |      12.0 |       7.1 |     5.8x |    1.7x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     103.9 |      34.8 |      25.9 |     4.0x |    1.3x |  |
| n-queens         | n=6 (4 sols, pure)   |      21.8 |       4.0 |       1.5 |    14.3x |    2.6x |  |
| n-queens         | n=7 (40 sols, pure)  |     108.1 |      11.9 |       6.1 |    17.9x |    2.0x |  |
| n-queens         | n=8 (92 sols, pure)  |     632.4 |      52.8 |      26.7 |    23.7x |    2.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     3.9x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.1 |      -1.0 |       0.0 |     2.0x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.5x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 39.3x vs the
reference Set, and 3.7x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is touched during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.

