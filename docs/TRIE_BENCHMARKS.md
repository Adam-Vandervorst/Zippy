# Trie Runtime Benchmarks

Measured with `TrieBenchmarks` on this worktree. Runtime times are average milliseconds per evaluation after two warmup runs. The first table excludes compilation/supercompilation and graph construction; rows labelled `process-sc` or `compile-pass` time the residual/compiled runtime. Runtime speedup cells and compile/run ratios are deliberately omitted for graphs that have been completely residualized to a one-node literal; use the compile+run column in the second table for those rows. The second table reports setup supercompilation time, graph compilation time, total compile time, compile/run ratio for non-residual graph execution, compile+`ROG execT` time, timed compile-stage totals, constant-folding eval time, and optimization-pass totals under explicit compile budgets. Graph optimization includes loop-invariant subgraph hoisting, push-out, and sharing. `ROG exec` is the legacy `RecursiveOpGraph` executor over `SpaceValue`; `evalZ` is the declarative zipper traversal evaluator that composes logical trie cursors and materializes only at the result boundary; `ROG execT` is the interned trie executor over `TrieSpace` and `List[Int]` path slots. Graph rows use fully optimized graphs: helper functions are inlined/expanded/lowered where possible, surviving `Call`s dispatch to optimized callee graphs, and graph-note cells list retained calls found in both the top graph and optimized callees. Recursive cycles are unsupported unless structurally certified as the paper SCC routine's strict three-way node partition.

## Runtime

| benchmark | variant | result paths | eval Set ms | ROG exec ms | evalTrie ms | evalZ ms | ROG execT ms | evalTrie / eval | evalZ / eval | evalZ / evalTrie | ROG exec / eval | ROG execT / eval | ROG execT / evalTrie | graph nodes | graph note |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| aunt | reference | 3 | 0.195 | 0.278 | 0.689 | 0.744 | 0.506 | 0.28 x | 0.26 x | 0.93 x | 0.70 x | 0.39 x | 1.36 x | 21 |  |
| aunt | process-sc static family | 3 | 0.051 | 0.183 | 0.563 | 1.034 | 0.242 | 0.09 x | 0.05 x | 0.54 x | 0.28 x | 0.21 x | 2.32 x | 20 |  |
| aunt synthetic | reference 60 people | 36 | 6.092 | 1.569 | 1.285 | 4.055 | 0.949 | 4.74 x | 1.50 x | 0.32 x | 3.88 x | 6.42 x | 1.35 x | 21 |  |
| aunt royal92 | reference royal92_simple.metta fallback | 3 | 0.108 | 0.083 | 0.077 | 0.126 | 0.062 | 1.41 x | 0.86 x | 0.61 x | 1.29 x | 1.72 x | 1.23 x | 21 |  |
| aunt synthetic | process-sc static family 24 people | 12 | 0.196 | 0.356 | 2.552 | 2.509 | 0.271 | 0.08 x | 0.08 x | 1.02 x | 0.55 x | 0.73 x | 9.43 x | 20 |  |
| graph two-hop | reference 90-chain | 264 | 6.780 | 1.967 | 0.956 | 2.321 | 0.673 | 7.09 x | 2.92 x | 0.41 x | 3.45 x | 10.08 x | 1.42 x | 15 |  |
| graph mutual | reference 90-chain | 0 | 5.913 | 1.797 | 0.574 | 0.838 | 0.301 | 10.30 x | 7.06 x | 0.69 x | 3.29 x | 19.62 x | 1.90 x | 15 |  |
| scc | paper divide-and-conquer | 2 | 0.723 | 0.579 | 1.368 | 5.684 | 0.384 | 0.53 x | 0.13 x | 0.24 x | 1.25 x | 1.88 x | 3.56 x | 54 | exec fallback Call dispatch to optimized callee graph(s): reachable, seedless_scc |
| datalog semi-naive | reference 24-chain | 300 | 357.808 | 0.008 | 7.850 | 16.439 | 0.002 | 45.58 x | 21.77 x | 0.48 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| datalog semi-naive | process-sc 24-chain | 300 | 321.318 | 22.131 | 11.766 | 4.378 | 5.418 | 27.31 x | 73.39 x | 2.69 x | 14.52 x | 59.30 x | 2.17 x | 6 | exec fallback Call dispatch to optimized callee graph(s): step352598575_sc1 |
| life | reference random 24x24 | 125 | 37.218 | 22.251 | 443.494 | 817.011 | 6.802 | 0.08 x | 0.05 x | 0.54 x | 1.67 x | 5.47 x | 65.20 x | 2,667 | exec fallback Call dispatch to optimized callee graph(s): neigh |
| life | compile-pass random 24x24 | 125 | 30.968 | 0.002 | 311.989 | 379.716 | 0.001 | 0.10 x | 0.08 x | 0.82 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| life | compile-pass random 24x24 initial literal | 125 | 0.001 | 0.001 | 0.048 | 0.057 | 0.001 | 0.02 x | 0.02 x | 0.84 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| temperature | NOAA committed slice | 12 | 0.004 | 0.003 | 0.010 | 0.023 | 0.007 | 0.37 x | 0.16 x | 0.42 x | 1.05 x | 0.49 x | 1.33 x | 3 |  |
| temperature | synthetic 32x64 | 448 | 1.526 | 1.507 | 0.016 | 0.044 | 0.011 | 92.64 x | 34.54 x | 0.37 x | 1.01 x | 136.56 x | 1.47 x | 3 |  |
| sliding puzzle | 2x2 pure source full frontier step | 12 | 5.974 | 0.001 | 4.890 | 8.070 | 0.001 | 1.22 x | 0.74 x | 0.61 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| sliding puzzle | 2x2 pure compile-pass full frontier step | 12 | 0.001 | 0.001 | 0.009 | 0.009 | 0.001 | 0.09 x | 0.09 x | 0.98 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| sliding puzzle | 3x3 pure source depth-8 step | 420 | 477.826 | 0.002 | 702.169 | n/a | 0.001 | 0.68 x | n/a | n/a | n/a | n/a | n/a | 1 | compiled away; use compile+run; direct evalZ source search tree exceeds the benchmark heap; use evalTrie/graph rows |
| sliding puzzle | 3x3 pure compile-pass depth-8 step | 420 | 0.001 | 0.001 | 0.417 | 0.420 | 0.001 | 0.00 x | 0.00 x | 0.99 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |
| sliding puzzle | 4x4 pure source depth-5 step | 202 | 805.180 | 0.033 | 1404.350 | n/a | 0.010 | 0.57 x | n/a | n/a | n/a | n/a | n/a | 1 | compiled away; use compile+run; direct evalZ source search tree exceeds the benchmark heap; use evalTrie/graph rows |
| n-queens | MORKL 8x8 source | 92 | 731.776 | 0.004 | 2576.853 | n/a | 0.001 | 0.28 x | n/a | n/a | n/a | n/a | n/a | 1 | compiled away; use compile+run; direct evalZ is currently omitted for the high-level source search tree; use compile-pass/graph rows |
| n-queens | MORKL 8x8 compile-pass | 92 | 0.001 | 0.001 | 0.065 | 0.075 | 0.001 | 0.02 x | 0.02 x | 0.86 x | n/a | n/a | n/a | 1 | compiled away; use compile+run |

## Compilation And Optimization

| benchmark | variant | prep compile ms | graph compile ms | total compile ms | compile/run | compile+ROG execT ms | lower+inline ms | source pass ms | const-fold eval ms | const-fold evalTrie ms | const-fold evalZ ms | const-fold execT ms | const-fold eval calls | const-fold evalTrie calls | const-fold evalZ calls | const-fold execT calls | graph transpile ms | graph optimize ms | source pass attempts | graph pass steps | budget ms sum | note |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| aunt | reference | n/a | 8.049 | 8.049 | 15.89 x | 8.556 | 0.171 | 1.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0 | 0 | 0 | 0 | 0.273 | 3.149 | 38 | 6 | 30000 | graph compile + optimized callees |
| aunt | process-sc static family | 61.688 | 3.367 | 65.055 | 268.43 x | 65.297 | 0.135 | 0.881 | 0.006 | 0.000 | 0.000 | 0.000 | 5 | 0 | 0 | 0 | 0.117 | 1.554 | 19 | 6 | 60000 | process SC setup; graph compile + optimized callees |
| aunt synthetic | reference 60 people | n/a | 2.995 | 2.995 | 3.16 x | 3.944 | 0.062 | 0.514 | 0.000 | 0.000 | 0.000 | 0.000 | 0 | 0 | 0 | 0 | 0.157 | 1.746 | 38 | 6 | 30000 | graph compile + optimized callees |
| aunt royal92 | reference royal92_simple.metta fallback | n/a | 2.852 | 2.852 | 45.66 x | 2.915 | 0.063 | 0.556 | 0.000 | 0.000 | 0.000 | 0.000 | 0 | 0 | 0 | 0 | 0.366 | 1.391 | 38 | 6 | 30000 | graph compile + optimized callees |
| aunt synthetic | process-sc static family 24 people | 8.876 | 2.207 | 11.083 | 40.96 x | 11.354 | 0.113 | 0.650 | 0.003 | 0.000 | 0.000 | 0.000 | 5 | 0 | 0 | 0 | 0.111 | 0.966 | 19 | 6 | 60000 | process SC setup; graph compile + optimized callees |
| graph two-hop | reference 90-chain | n/a | 2.934 | 2.934 | 4.36 x | 3.607 | 0.024 | 0.317 | 0.021 | 0.000 | 0.000 | 0.000 | 2 | 0 | 0 | 0 | 0.061 | 1.848 | 57 | 9 | 30000 | graph compile + optimized callees |
| graph mutual | reference 90-chain | n/a | 2.232 | 2.232 | 7.41 x | 2.534 | 0.024 | 0.173 | 0.000 | 0.000 | 0.000 | 0.000 | 0 | 0 | 0 | 0 | 0.046 | 1.518 | 38 | 9 | 30000 | graph compile + optimized callees |
| scc | paper divide-and-conquer | n/a | 28.111 | 28.111 | 73.23 x | 28.495 | 1.249 | 16.198 | 0.776 | 0.000 | 0.000 | 0.000 | 146 | 0 | 0 | 0 | 1.213 | 4.751 | 133 | 12 | 90000 | graph compile + optimized callees |
| datalog semi-naive | reference 24-chain | n/a | 20.730 | 20.730 | n/a | 20.731 | 0.080 | 19.432 | 0.367 | 17.293 | 0.000 | 0.000 | 9 | 1 | 0 | 0 | 0.006 | 0.188 | 38 | 3 | 30000 | graph compile + optimized callees |
| datalog semi-naive | process-sc 24-chain | 86.912 | 8.493 | 95.405 | 17.61 x | 100.823 | 0.068 | 1.549 | 0.004 | 0.000 | 0.000 | 0.000 | 10 | 0 | 0 | 0 | 0.234 | 5.555 | 38 | 12 | 90000 | process SC setup; graph compile + optimized callees |
| life | reference random 24x24 | n/a | 4674.280 | 4674.280 | 687.17 x | 4681.082 | 0.352 | 4302.756 | 0.395 | 0.000 | 0.000 | 0.000 | 1384 | 0 | 0 | 0 | 2.440 | 363.993 | 114 | 12 | 60000 | graph compile + optimized callees |
| life | compile-pass random 24x24 | 108.793 | 20.957 | 129.750 | n/a | 129.750 | 2.506 | 64.385 | 20.557 | 0.000 | 0.000 | 0.000 | 114 | 0 | 0 | 0 | 1.871 | 43.935 | 95 | 12 | 60000 | compile-pass setup; graph compile + optimized callees |
| life | compile-pass random 24x24 initial literal | 113.857 | 0.391 | 114.248 | n/a | 114.249 | 0.326 | 111.235 | 98.397 | 0.000 | 0.000 | 0.000 | 73 | 0 | 0 | 0 | 0.017 | 0.463 | 57 | 6 | 60000 | compile-pass setup with initial grid literal; graph compile + optimized callees |
| temperature | NOAA committed slice | n/a | 0.420 | 0.420 | 57.72 x | 0.427 | 0.029 | 0.068 | 0.008 | 0.000 | 0.000 | 0.000 | 5 | 0 | 0 | 0 | 0.005 | 0.065 | 38 | 3 | 30000 | graph compile + optimized callees |
| temperature | synthetic 32x64 | n/a | 0.285 | 0.285 | 25.55 x | 0.297 | 0.013 | 0.059 | 0.013 | 0.000 | 0.000 | 0.000 | 5 | 0 | 0 | 0 | 0.004 | 0.053 | 38 | 3 | 30000 | graph compile + optimized callees |
| sliding puzzle | 2x2 pure source full frontier step | n/a | 2.941 | 2.941 | n/a | 2.942 | 0.110 | 2.020 | 1.184 | 0.000 | 0.000 | 0.000 | 65 | 0 | 0 | 0 | 0.003 | 0.067 | 38 | 3 | 30000 | graph compile + optimized callees |
| sliding puzzle | 2x2 pure compile-pass full frontier step | 10.298 | 0.389 | 10.686 | n/a | 10.687 | 0.290 | 9.587 | 4.075 | 0.000 | 0.000 | 0.000 | 66 | 0 | 0 | 0 | 0.004 | 0.101 | 57 | 3 | 60000 | compile-pass setup; graph compile + optimized callees |
| sliding puzzle | 3x3 pure source depth-8 step | n/a | 51.759 | 51.759 | n/a | 51.760 | 0.142 | 49.903 | 46.225 | 0.000 | 0.000 | 0.000 | 176 | 0 | 0 | 0 | 0.004 | 0.084 | 38 | 3 | 30000 | graph compile + optimized callees |
| sliding puzzle | 3x3 pure compile-pass depth-8 step | 141.228 | 0.445 | 141.673 | n/a | 141.674 | 0.608 | 139.430 | 123.237 | 0.000 | 0.000 | 0.000 | 177 | 0 | 0 | 0 | 0.002 | 0.130 | 57 | 3 | 60000 | compile-pass setup; graph compile + optimized callees |
| sliding puzzle | 4x4 pure source depth-5 step | n/a | 76.436 | 76.436 | n/a | 76.446 | 0.203 | 73.696 | 58.926 | 0.000 | 0.000 | 0.000 | 341 | 0 | 0 | 0 | 0.005 | 0.121 | 38 | 3 | 30000 | graph compile + optimized callees |
| n-queens | MORKL 8x8 source | n/a | 545.286 | 545.286 | n/a | 545.287 | 0.145 | 543.908 | 537.409 | 0.000 | 0.000 | 0.000 | 130 | 0 | 0 | 0 | 0.004 | 0.127 | 38 | 3 | 30000 | graph compile + optimized callees |
| n-queens | MORKL 8x8 compile-pass | 644.473 | 0.485 | 644.958 | n/a | 644.959 | 0.503 | 643.274 | 628.338 | 0.000 | 0.000 | 0.000 | 131 | 0 | 0 | 0 | 0.030 | 0.089 | 57 | 3 | 60000 | compile-pass setup; graph compile + optimized callees |

| benchmark | variant | result | ms | note |
|---|---:|---:|---:|---|
| n-queens bit reference | n=8 | 92 | 0.016 | independent reference, not MORKL eval |
| n-queens bit reference | n=9 | 352 | 0.068 | independent reference, not MORKL eval |
| n-queens bit reference | n=10 | 724 | 0.245 | independent reference, not MORKL eval |
| n-queens bit reference | n=11 | 2680 | 1.095 | independent reference, not MORKL eval |
| n-queens bit reference | n=12 | 14200 | 5.740 | independent reference, not MORKL eval |

## Interpretation

The trie evaluator remains strongest on native path algebra with shared prefixes, joins, restriction, unwrap, and first-symbol iteration. The direct `execT` backend compounds that advantage when the graph is lowered to native ops and optimized callee graphs because it avoids rebuilding old `PathValue` and `SpaceValue` intermediates.

`evalZ` is included as a correctness-backed zipper traversal runtime. Generic iteration now joins materialized branch tries directly at the final boundary, keeping nonrecursive scaling near `evalTrie`; union-saturating recursion is lowered and measured directly. Structurally positive, productive steps use prefix-demand cells, while state-negative semi-naive Datalog uses lazy exact synchronous rounds executed directly in native trie algebra. The SCC row executes the paper's well-founded pivot/partition recursion with masked reachability lowered to a fixpoint. The separate `ZIPPER_LARGE_BENCHMARKS.md` report contains larger nonrecursive scaling and product-selector rows. Direct source n-queens remains omitted for `evalZ` with an explicit note because that high-level search tree still needs a dedicated recursive zipper strategy.

The pure Game-of-Life source is now intentionally a lowering benchmark: direct `evalTrie` still interprets the high-level relation program, while the graph backend lowers `Range`, `Unwrap`, joins, and literal coordinate relations into direct operations; use the `ROG execT` and compile+`ROG execT` columns for the lowered result.

Graph timings are intentionally conservative about semantics. Raw routine calls are not timed as raw helper graphs; helper routines are inlined/expanded and lowered before graph execution when possible, and surviving calls use optimized callee graphs. Fixpoint lowering handles both single-state and invariant-parameter union-saturating shapes. Recursive residual cycles remain unsupported unless the structural checker certifies the paper SCC routine's three strict node partitions; that certified cycle dispatches through optimized callee graphs.

Compilation is now explicitly bounded by wall-clock budgets as well as structural caps. Source normalization records every pass attempt, graph optimization records `hoist_loop_invariant_subgraphs`, `push_out`, and `optimize_sharing` per round, constant folding records eval/evalTrie/evalZ/execT time and call counts, and the compilation table separates setup SC time, lowering/inlining time, source-pass time, graph-build time, graph-optimization time, compile/run ratio, and compile+run time so runtime speedups are not mistaken for free compilation.

`budget ms sum` is the sum of the independent compile invocation budgets used for a row, including optimized callee-graph compiles when present; it is not elapsed time and not a single shared deadline across all rows.

Rows marked `compiled away; use compile+run` have been fully residualized to a one-node literal by the compile pipeline before execution. Their executor timings are still shown as an implementation sanity check, but their graph speedup factors are intentionally reported as `n/a`; the meaningful number is the compile+`ROG execT` total in the compilation table.

The independent bit-recursive n-queens rows are scaling references, not MORKL runtime rows. They record the known targets through 12x12 while the pure MORKL path-algebra program is executed exactly at 8x8 and compiled/residualized for graph execution.
