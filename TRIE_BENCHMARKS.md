# Trie Runtime Benchmarks

Measured with `TrieBenchmarks` on this worktree. Runtime times are average milliseconds per evaluation after two warmup runs. The first table excludes compilation/supercompilation and graph construction; rows labelled `process-sc` or `compile-pass` time the residual/compiled runtime. Runtime speedup cells and compile/run ratios are deliberately omitted for graphs that have been completely residualized to a one-node literal; use the compile+run column in the second table for those rows. The second table reports setup supercompilation time, graph compilation time, total compile time, compile/run ratio for non-residual graph execution, compile+`ROG execT` time, timed compile-stage totals, constant-folding eval time, and optimization-pass totals under explicit compile budgets. Graph optimization includes loop-invariant subgraph hoisting, push-out, and sharing. `ROG exec` is the legacy `RecursiveOpGraph` executor over `SpaceValue`; `evalZ` is the declarative zipper traversal evaluator that composes logical trie cursors and materializes only at the result boundary; `ROG execT` is the interned trie executor over `TrieSpace` and `List[Int]` path slots. Graph rows use fully optimized graphs: helper functions are inlined/expanded/lowered where possible, any surviving nonrecursive `Call`s dispatch to optimized callee graphs, and graph-note cells list retained calls found in both the top graph and optimized callee graphs. Recursive source `Call` cycles that survive lowering are marked unsupported.

## Runtime

| benchmark | variant | result paths | eval Set ms | ROG exec ms | evalTrie ms | evalZ ms | ROG execT ms | evalTrie / eval | evalZ / eval | evalZ / evalTrie | ROG exec / eval | ROG execT / eval | ROG execT / evalTrie | graph nodes | graph note |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| aunt | reference | 3 | 0.085 | 0.197 | 0.209 | 0.610 | 0.159 | 0.41 x | 0.14 x | 0.34 x | 0.43 x | 0.54 x | 1.32 x | 21 |  |
| aunt | process-sc static family | 3 | 0.057 | 0.147 | 0.118 | 0.717 | 0.081 | 0.48 x | 0.08 x | 0.16 x | 0.39 x | 0.70 x | 1.45 x | 20 |  |
| aunt synthetic | reference 60 people | 36 | 3.148 | 1.342 | 1.236 | 2.275 | 0.545 | 2.55 x | 1.38 x | 0.54 x | 2.35 x | 5.77 x | 2.27 x | 21 |  |
| aunt royal92 | reference royal92_simple.metta 3010 people | 2,989 | 4146.363 | 600.239 | 4.866 | 20.999 | 8.042 | 852.13 x | 197.46 x | 0.23 x | 6.91 x | 515.61 x | 0.61 x | 21 |  |
| aunt synthetic | process-sc static family 24 people | 12 | 0.189 | 0.218 | 0.572 | 0.677 | 0.110 | 0.33 x | 0.28 x | 0.84 x | 0.86 x | 1.71 x | 5.20 x | 20 |  |
| graph two-hop | reference 90-chain | 264 | 3.750 | 0.687 | 1.859 | 2.140 | 0.076 | 2.02 x | 1.75 x | 0.87 x | 5.46 x | 49.53 x | 24.56 x | 13 |  |
| graph mutual | reference 90-chain | 0 | 3.243 | 0.838 | 0.905 | 0.878 | 0.089 | 3.58 x | 3.69 x | 1.03 x | 3.87 x | 36.28 x | 10.13 x | 15 |  |
| datalog semi-naive | reference 24-chain | 300 | 258.456 | 0.002 | 25.031 | 31.918 | 0.002 | 10.33 x | 8.10 x | 0.78 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| datalog semi-naive | process-sc 24-chain | 300 | 245.329 | 11.223 | 8.259 | 3.861 | 2.131 | 29.70 x | 63.54 x | 2.14 x | 21.86 x | 115.14 x | 3.88 x | 6 |  |
| life | reference random 24x24 | 125 | 23.633 | 14.909 | 470.725 | 478.288 | 3.711 | 0.05 x | 0.05 x | 0.98 x | 1.59 x | 6.37 x | 126.84 x | 2,667 |  |
| life | compile-pass random 24x24 | 125 | 20.749 | 0.001 | 469.169 | 486.686 | 0.001 | 0.04 x | 0.04 x | 0.96 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| life | compile-pass random 24x24 initial literal | 125 | 0.000 | 0.001 | 0.033 | 0.033 | 0.001 | 0.01 x | 0.01 x | 1.00 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| temperature | NOAA committed slice | 430 | 0.160 | 0.073 | 0.005 | 0.041 | 0.001 | 35.27 x | 3.89 x | 0.11 x | 2.20 x | 129.02 x | 3.66 x | 3 |  |
| temperature | synthetic 32x64 | 448 | 1.041 | 0.991 | 0.006 | 0.057 | 0.001 | 170.81 x | 18.21 x | 0.11 x | 1.05 x | 773.20 x | 4.53 x | 3 |  |
| sliding puzzle | 2x2 pure source full frontier step | 12 | 4.517 | 0.001 | 5.825 | 8.984 | 0.001 | 0.78 x | 0.50 x | 0.65 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| sliding puzzle | 2x2 pure compile-pass full frontier step | 12 | 0.001 | 0.001 | 0.002 | 0.003 | 0.001 | 0.21 x | 0.20 x | 0.93 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| sliding puzzle | 3x3 pure source depth-8 step | 420 | 293.509 | 0.001 | 559.090 | 625.603 | 0.001 | 0.52 x | 0.47 x | 0.89 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| sliding puzzle | 3x3 pure compile-pass depth-8 step | 420 | 0.000 | 0.001 | 0.166 | 0.168 | 0.001 | 0.00 x | 0.00 x | 0.99 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| sliding puzzle | 4x4 pure source depth-5 step | 202 | 485.615 | 0.001 | 1002.573 | 1107.178 | 0.001 | 0.48 x | 0.44 x | 0.91 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| n-queens | MORKL 8x8 source | 92 | 451.923 | 0.001 | 1102.512 | n/a | 0.001 | 0.41 x | n/a | n/a | n/a | n/a | n/a | 1 | compiled away; use compile+run; direct evalZ is currently omitted for the high-level source search tree; use compile-pass/graph rows |
| n-queens | MORKL 8x8 compile-pass | 92 | 0.001 | 0.001 | 0.035 | 0.028 | 0.001 | 0.02 x | 0.02 x | 1.24 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |

## Compilation And Optimization

| benchmark | variant | prep compile ms | graph compile ms | total compile ms | compile/run | compile+ROG execT ms | lower+inline ms | source pass ms | const-fold eval ms | const-fold evalTrie ms | const-fold evalZ ms | const-fold execT ms | const-fold eval calls | const-fold evalTrie calls | const-fold evalZ calls | const-fold execT calls | graph transpile ms | graph optimize ms | source pass attempts | graph pass steps | budget ms sum | note |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| aunt | reference | n/a | 2.677 | 2.677 | 16.89 x | 2.836 | 0.062 | 0.267 | 0.000 | 0.000 | 0.000 | 0.000 | 0 | 0 | 0 | 0 | 0.121 | 0.968 | 34 | 6 | 30000 | graph compile + optimized callees |
| aunt | process-sc static family | 31.252 | 4.887 | 36.139 | 444.65 x | 36.220 | 2.820 | 0.376 | 0.008 | 0.000 | 0.000 | 0.000 | 5 | 0 | 0 | 0 | 0.072 | 0.965 | 17 | 6 | 60000 | process SC setup; graph compile + optimized callees |
| aunt synthetic | reference 60 people | n/a | 2.032 | 2.032 | 3.73 x | 2.577 | 0.064 | 1.020 | 0.000 | 0.000 | 0.000 | 0.000 | 0 | 0 | 0 | 0 | 0.064 | 0.586 | 34 | 6 | 30000 | graph compile + optimized callees |
| aunt royal92 | reference royal92_simple.metta 3010 people | n/a | 1.669 | 1.669 | 0.21 x | 9.711 | 0.047 | 0.171 | 0.000 | 0.000 | 0.000 | 0.000 | 0 | 0 | 0 | 0 | 0.089 | 0.969 | 34 | 6 | 30000 | graph compile + optimized callees |
| aunt synthetic | process-sc static family 24 people | 4.763 | 1.415 | 6.178 | 56.19 x | 6.287 | 0.094 | 0.273 | 0.003 | 0.000 | 0.000 | 0.000 | 5 | 0 | 0 | 0 | 0.050 | 0.740 | 17 | 6 | 60000 | process SC setup; graph compile + optimized callees |
| graph two-hop | reference 90-chain | n/a | 0.914 | 0.914 | 12.07 x | 0.990 | 0.018 | 0.086 | 0.000 | 0.000 | 0.000 | 0.000 | 0 | 0 | 0 | 0 | 0.019 | 0.527 | 34 | 9 | 30000 | graph compile + optimized callees |
| graph mutual | reference 90-chain | n/a | 0.870 | 0.870 | 9.73 x | 0.959 | 0.019 | 0.075 | 0.000 | 0.000 | 0.000 | 0.000 | 0 | 0 | 0 | 0 | 0.020 | 0.498 | 34 | 9 | 30000 | graph compile + optimized callees |
| datalog semi-naive | reference 24-chain | n/a | 21.994 | 21.994 | n/a | 21.995 | 0.677 | 20.495 | 0.266 | 17.780 | 0.000 | 0.000 | 9 | 1 | 0 | 0 | 0.004 | 0.154 | 34 | 3 | 30000 | graph compile + optimized callees |
| datalog semi-naive | process-sc 24-chain | 40.358 | 6.196 | 46.554 | 21.85 x | 48.685 | 0.177 | 1.308 | 0.002 | 0.000 | 0.000 | 0.000 | 2 | 0 | 0 | 0 | 0.234 | 2.529 | 34 | 12 | 90000 | process SC setup; graph compile + optimized callees |
| life | reference random 24x24 | n/a | 2709.955 | 2709.955 | 730.20 x | 2713.666 | 0.567 | 2435.641 | 0.304 | 0.000 | 0.000 | 0.000 | 1384 | 0 | 0 | 0 | 1.814 | 267.361 | 102 | 12 | 60000 | graph compile + optimized callees |
| life | compile-pass random 24x24 | 96.975 | 13.437 | 110.412 | n/a | 110.412 | 1.509 | 61.747 | 9.908 | 0.000 | 0.000 | 0.000 | 154 | 0 | 0 | 0 | 1.278 | 30.806 | 85 | 12 | 60000 | compile-pass setup; graph compile + optimized callees |
| life | compile-pass random 24x24 initial literal | 88.769 | 0.341 | 89.110 | n/a | 89.111 | 0.200 | 87.626 | 81.831 | 0.000 | 0.000 | 0.000 | 53 | 0 | 0 | 0 | 0.016 | 0.351 | 51 | 6 | 60000 | compile-pass setup with initial grid literal; graph compile + optimized callees |
| temperature | NOAA committed slice | n/a | 0.329 | 0.329 | 264.71 x | 0.330 | 0.020 | 0.041 | 0.005 | 0.000 | 0.000 | 0.000 | 5 | 0 | 0 | 0 | 0.002 | 0.060 | 34 | 3 | 30000 | graph compile + optimized callees |
| temperature | synthetic 32x64 | n/a | 0.200 | 0.200 | 148.32 x | 0.201 | 0.007 | 0.038 | 0.008 | 0.000 | 0.000 | 0.000 | 5 | 0 | 0 | 0 | 0.003 | 0.052 | 34 | 3 | 30000 | graph compile + optimized callees |
| sliding puzzle | 2x2 pure source full frontier step | n/a | 1.997 | 1.997 | n/a | 1.998 | 0.107 | 1.396 | 0.930 | 0.000 | 0.000 | 0.000 | 81 | 0 | 0 | 0 | 0.001 | 0.065 | 34 | 3 | 30000 | graph compile + optimized callees |
| sliding puzzle | 2x2 pure compile-pass full frontier step | 12.312 | 0.192 | 12.504 | n/a | 12.505 | 0.206 | 11.557 | 6.780 | 0.000 | 0.000 | 0.000 | 82 | 0 | 0 | 0 | 0.001 | 0.069 | 51 | 3 | 60000 | compile-pass setup; graph compile + optimized callees |
| sliding puzzle | 3x3 pure source depth-8 step | n/a | 29.038 | 29.038 | n/a | 29.038 | 0.125 | 28.408 | 27.065 | 0.000 | 0.000 | 0.000 | 224 | 0 | 0 | 0 | 0.001 | 0.070 | 34 | 3 | 30000 | graph compile + optimized callees |
| sliding puzzle | 3x3 pure compile-pass depth-8 step | 79.985 | 0.201 | 80.187 | n/a | 80.187 | 0.663 | 78.827 | 66.188 | 0.000 | 0.000 | 0.000 | 225 | 0 | 0 | 0 | 0.001 | 0.070 | 51 | 3 | 60000 | compile-pass setup; graph compile + optimized callees |
| sliding puzzle | 4x4 pure source depth-5 step | n/a | 44.926 | 44.926 | n/a | 44.927 | 0.179 | 43.039 | 36.178 | 0.000 | 0.000 | 0.000 | 437 | 0 | 0 | 0 | 0.001 | 0.057 | 34 | 3 | 30000 | graph compile + optimized callees |
| n-queens | MORKL 8x8 source | n/a | 348.417 | 348.417 | n/a | 348.418 | 0.125 | 347.626 | 340.743 | 0.000 | 0.000 | 0.000 | 178 | 0 | 0 | 0 | 0.001 | 0.053 | 34 | 3 | 30000 | graph compile + optimized callees |
| n-queens | MORKL 8x8 compile-pass | 418.198 | 0.193 | 418.391 | n/a | 418.392 | 0.567 | 417.399 | 401.669 | 0.000 | 0.000 | 0.000 | 179 | 0 | 0 | 0 | 0.001 | 0.059 | 51 | 3 | 60000 | compile-pass setup; graph compile + optimized callees |

| benchmark | variant | result | ms | note |
|---|---:|---:|---:|---|
| n-queens bit reference | n=8 | 92 | 0.033 | independent reference, not MORKL eval |
| n-queens bit reference | n=9 | 352 | 0.039 | independent reference, not MORKL eval |
| n-queens bit reference | n=10 | 724 | 0.180 | independent reference, not MORKL eval |
| n-queens bit reference | n=11 | 2680 | 0.730 | independent reference, not MORKL eval |
| n-queens bit reference | n=12 | 14200 | 4.027 | independent reference, not MORKL eval |

## Interpretation

The trie evaluator remains strongest on native path algebra with shared prefixes, joins, restriction, unwrap, and first-symbol iteration. The direct `execT` backend compounds that advantage when the graph is lowered to native ops and optimized callee graphs because it avoids rebuilding old `PathValue` and `SpaceValue` intermediates.

`evalZ` is included as a correctness-backed zipper traversal prototype, not yet as the winning runtime for every source shape. Memoized virtual zippers now keep the sliding-puzzle source rows near `evalTrie`, and top-level union-saturating self recursion is rejected as unsupported rather than falling back to concrete `evalTrie` materialization. The separate `ZIPPER_LARGE_BENCHMARKS.md` report contains larger asymptotic product-selector rows where zipper traversal avoids broad intermediate scans. Direct source n-queens remains omitted for `evalZ` with an explicit note because that high-level search tree still needs a dedicated recursive zipper strategy.

The pure Game-of-Life source is now intentionally a lowering benchmark: direct `evalTrie` still interprets the high-level relation program, while the graph backend lowers `Range`, `Unwrap`, joins, and literal coordinate relations into direct operations; use the `ROG execT` and compile+`ROG execT` columns for the lowered result.

Graph timings are intentionally conservative about semantics. Raw routine calls are not timed as raw helper graphs; helper routines are inlined/expanded and lowered before graph execution when possible, and surviving nonrecursive calls use optimized callee graphs. The fixpoint lowering handles the `Routines.fixpoint` union-saturating shape, while recursive residual call cycles still need dedicated lowering before `exec`/`execT` can be reported honestly.

Compilation is now explicitly bounded by wall-clock budgets as well as structural caps. Source normalization records every pass attempt, graph optimization records `hoist_loop_invariant_subgraphs`, `push_out`, and `optimize_sharing` per round, constant folding records eval/evalTrie/evalZ/execT time and call counts, and the compilation table separates setup SC time, lowering/inlining time, source-pass time, graph-build time, graph-optimization time, compile/run ratio, and compile+run time so runtime speedups are not mistaken for free compilation.

`budget ms sum` is the sum of the independent compile invocation budgets used for a row, including optimized callee-graph compiles when present; it is not elapsed time and not a single shared deadline across all rows.

Rows marked `compiled away; use compile+run` have been fully residualized to a one-node literal by the compile pipeline before execution. Their executor timings are still shown as an implementation sanity check, but their graph speedup factors are intentionally reported as `n/a`; the meaningful number is the compile+`ROG execT` total in the compilation table.

The independent bit-recursive n-queens rows are scaling references, not MORKL runtime rows. They record the known targets through 12x12 while the pure MORKL path-algebra program is executed exactly at 8x8 and compiled/residualized for graph execution.
