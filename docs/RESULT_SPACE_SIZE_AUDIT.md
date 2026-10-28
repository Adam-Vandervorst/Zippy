# Result-space size audit

The final mixed operation-law plus Z3 runs were sound: every concrete result was at least its evaluated lower bound and no larger than its finite evaluated upper bound. No lower bound was unknown, and no refined bound weakened the original interval baseline.

## Mixed refinement and baseline guarantee

Boolean set structure (`union`, `intersection`, and `subtraction`) is translated to a Boolean formula. For at most eight distinct opaque set atoms, Z3 optimizes the cardinality of the selected Venn regions subject to every atom's compositional lower and upper bounds. A separate Boolean query proves subset and disjointness relations used to simplify correlated Boolean components nested inside other operations. Selector operations now export subset/disjointness facts directly into the Venn graph, literal relations export maximum prefix-fiber degrees, and nested iteration over an outer tail binding is flattened as a union-map when the inner body does not inspect its tail set. Explicit set laws carry finite bounds through iteration, composition, restriction, unwrap, range, and closures; they are stated in [RESULT_SPACE_SIZE_LAWS.md](RESULT_SPACE_SIZE_LAWS.md).

The original compositional estimate remains the mandatory fallback. A refined lower is combined with the baseline using `max`, and a refined upper using `min`; solver failure, timeout, an oversized problem, or a missing executable returns the baseline. The audit independently evaluates both estimates on every observation and fails if the refined lower is smaller, the refined upper is larger, or a finite baseline upper becomes unbounded. Thus the non-regression property is checked pointwise on exactly the same sets, rather than inferred from aggregate percentages.

The default limits are eight set atoms, 256 Boolean nodes, and one second per solver process. Expressions beyond those limits retain the linear baseline. The solver executable and limits are configurable with `morkl.z3`, `morkl.z3.maxCardinalityAtoms`, `morkl.z3.maxBooleanNodes`, and `morkl.z3.timeoutMillis`.

| Corpus | Upper improved over same-set baseline | Lower improved over same-set baseline | Baseline weakening |
|---|---:|---:|---:|
| Final full test suite | 15,548 (3.17%) | 13,493 (2.75%) | 0 |
| Canonical random corpus | 335 (33.50%) | 103 (10.30%) | 0 |

On the canonical random corpus, exact finite uppers increased from 301 to 347, exact lowers from 205 to 233, and all 37 formerly unbounded uppers became finite. Mean finite upper gap fell from 23,106,409.808 to 13,924.974 paths; mean lower gap fell from 3.904 to 3.686 paths.

### Strictly paired canonical 1,000 comparison

Both analyses were evaluated in one process over one shared vector returned by `SpaceFuzzerCorpus.generate(1000, 20260708L, 5, 400)`. Each program used exactly `S"x" -> record.example.arg`; neither side regenerated or changed an input. The ordered SHA-256 over `(id, program.show, sorted input paths, sorted expected-result paths)` is `3b2d244cfef1f12bd0988b5d1f88d1bd66ee13e74b8d6de5d97eb44b0d940046`. The 1,000 inputs contain 6,191 paths in total (minimum 1, maximum 27, mean 6.191), and the programs contain 16,395 AST nodes (minimum 2, maximum 47).

The baseline side exactly reproduces the earlier published baseline totals, including both means. This confirms that this is the same corpus and the same inputs rather than merely the same generator parameters.

| Metric | Baseline | Mixed refined | Paired change |
|---|---:|---:|---:|
| Finite upper | 963 (96.30%) | 1,000 (100.00%) | +37 |
| Unbounded upper | 37 | 0 | -37 |
| Exact finite upper | 301 (31.26%) | 347 (34.70%) | +46 |
| Exact lower | 205 (20.50%) | 233 (23.30%) | +28 |
| Mean finite upper gap | 23,106,409.808 | 13,924.974 | finite populations differ by 37 |
| Mean lower gap | 3.904 | 3.686 | -0.218 |

On the identical 963 programs with finite uppers on both sides, the mean upper gap fell from 23,106,409.808 to 1,278.962, a total reduction of 22,250,241,005 paths. Of all 1,000 pairs, 298 finite uppers tightened, all 37 unbounded uppers became finite, 103 lowers tightened, 665 uppers were unchanged, and 897 lowers were unchanged. There were zero pointwise regressions.

| Program | Input paths | Actual | Baseline upper | Refined upper | Reduction |
|---:|---:|---:|---:|---:|---:|
| 55 | 7 | 3 | 20,661,046,784 | 3,136 | 20,661,043,648 |
| 486 | 9 | 1 | 1,549,681,956 | 1,458 | 1,549,680,498 |
| 448 | 8 | 7 | 23,887,876 | 331,780 | 23,556,096 |
| 173 | 8 | 3 | 12,922,650 | 8,190 | 12,914,460 |
| 315 | 10 | 10 | 1,020,105 | 12,105 | 1,008,000 |

| Program | Input paths | Actual | Baseline lower | Refined lower | Increase |
|---:|---:|---:|---:|---:|---:|
| 85 | 27 | 39 | 0 | 27 | 27 |
| 527 | 12 | 84 | 0 | 12 | 12 |
| 153 | 9 | 36 | 0 | 9 | 9 |
| 280 | 9 | 99 | 0 | 9 | 9 |
| 966 | 9 | 19 | 0 | 9 | 9 |

### Boolean-only larger-program topology diagnosis

This diagnostic predates the mixed operation laws and isolates the Boolean solver. Increasing the ordinary fuzzer depth makes the complete programs much larger, but it does not make their connected Boolean constraint graphs proportionally larger. Operators such as iteration, composition, restriction, unwrap, range, and closures split the expression into opaque cardinality atoms. Consequently Z3 continues to receive small Boolean islands even when the surrounding AST exceeds 500 nodes.

| Maximum generator depth | Mean AST nodes | Maximum AST nodes | Maximum Boolean nodes/component | Maximum atoms/component | Z3-eligible programs | Upper improved | Lower improved |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 5 | 16.40 | 47 | 10 | 9 | 264 | 88 | 12 |
| 7 | 29.04 | 118 | 12 | 12 | 347 | 78 | 2 |
| 9 | 42.08 | 242 | 16 | 15 | 366 | 77 | 10 |
| 12 | 93.72 | 547 | 18 | 19 | 473 | 25 | 3 |

Every row contains 1,000 programs generated with seed `20260708L` and maximum concrete result 400. All are paired baseline/refined comparisons with zero weakened bounds. At depth 12, 275 of the 296 programs having at least 128 AST nodes are technically Z3-eligible, but only ten upper and one lower bounds improve. The local Boolean refinements are usually dominated by much looser opaque iteration/product bounds higher in the expression.

The analysis/evaluation cost also rises without a commensurate aggregate benefit: baseline versus refined totals were 35.3/437.5 ms at depth 5, 49.3/729.8 ms at depth 7, 52.8/616.0 ms at depth 9, and 48.5/970.6 ms at depth 12.

### Connected-Boolean control corpus

To distinguish solver weakness from generator topology, a second corpus deliberately formed one connected correlated Boolean component from eight set atoms. It contains 240 programs, 20 for each combination of 33, 65, 129, or 257 full AST nodes and union absorption, intersection absorption, or difference cancellation.

| Metric | Baseline | Z3 refined |
|---|---:|---:|
| Upper bounds improved | — | 204/240 (85.0%) |
| Lower bounds improved | — | 50/240 (20.8%) |
| Mean upper gap | 22.463 | 4.608 |
| Mean lower gap | 8.142 | 6.383 |
| Total analysis/evaluation time | 19.6 ms | 10,949.7 ms |

Thus the similar aggregate results on `SpaceFuzzerCorpus` are mainly real evidence about the current abstraction boundary: Z3 is effective when it sees a connected correlated set formula, but most large MORKL programs are represented as many small Boolean components surrounding opaque higher-order operators. The control also exposes an implementation problem: repeatedly launching relation queries during bottom-up normalization is roughly 559× slower than the baseline on dense connected graphs. A production constraint-graph implementation should encode each connected component once, share subformula variables, and issue one incremental solver session rather than one process/query per local relation.

### Fully optimized-program graphs

The same four deterministic corpora were then fully normalized with `Supercompiler.normalize`. Every optimized expression was evaluated on the original input and checked equal to its original expected result before its constraint graph was analyzed. The operation-law refinement described in [RESULT_SPACE_SIZE_LAWS.md](RESULT_SPACE_SIZE_LAWS.md) was enabled on both raw and optimized graphs while the original interval estimate remained the pointwise baseline.

| Depth | Raw mean/max AST | Optimized mean/max AST | Programs changed | Max Boolean component raw→optimized | Eligible raw→optimized | Repetition removed | Improvements raw U/L | Improvements optimized U/L | Optimized exact U/L |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 5 | 16.40 / 47 | 12.56 / 65 | 837 | 10→7 | 264→19 | 248 | 278 / 101 | 196 / 98 | 365 / 253 |
| 7 | 29.04 / 118 | 20.74 / 96 | 859 | 12→12 | 347→28 | 321 | 323 / 81 | 239 / 78 | 392 / 305 |
| 9 | 42.08 / 242 | 27.76 / 157 | 788 | 16→8 | 366→36 | 334 | 313 / 89 | 230 / 82 | 467 / 357 |
| 12 | 93.72 / 547 | 54.47 / 415 | 792 | 18→14 | 473→45 | 424 | 249 / 92 | 195 / 95 | 482 / 400 |

Normalization removes the expected degeneracies: depending on depth, 248–424 programs lose repeated Boolean atoms, and Z3-eligible Boolean correlation drops by roughly an order of magnitude. Tightening nevertheless remains common because the mixed graph now carries explicit laws through iteration, composition, restriction, unwrap, range, and closures. At depth 12 only 45 optimized programs retain a Z3-eligible repeated Boolean component, yet 195 upper and 95 lower bounds improve over the unchanged baseline.

Optimization plus analysis was also cheaper than analyzing the larger raw graph in the final run. At depths 5, 7, 9, and 12, normalize/raw-analysis/optimized-analysis totals were respectively 195.7/515.4/174.7 ms, 121.9/557.2/227.0 ms, 117.2/426.2/222.1 ms, and 262.7/759.3/261.4 ms. These totals include evaluating both baseline and refined bounds and benefit from the solver cache, so they are diagnostic rather than isolated microbenchmarks.

### Analyzer asymptotics

The linear correlation scan also records whether the graph contains any operation-law opportunity. Pure uncorrelated Boolean trees therefore reuse the already computed baseline instead of traversing the tree a second time. On balanced unions of distinct leaves, the final mixed analyzer stays at baseline cost and preserves linear scaling:

| Leaves | Baseline ms | Mixed refined ms | Refined/baseline |
|---:|---:|---:|---:|
| 1,024 | 0.1951 | 0.1606 | 0.82× |
| 2,048 | 0.3118 | 0.3195 | 1.02× |
| 4,096 | 0.6465 | 0.6497 | 1.01× |
| 8,192 | 1.6333 | 1.5865 | 0.97× |
| 16,384 | 4.0320 | 4.0126 | 1.00× |
| 32,768 | 8.5766 | 8.6985 | 1.01× |

These measurements cover graph construction only. Trie execution does not call this optional analysis, so executor asymptotics and the previously reported non-long executor benchmarks are unchanged.

## Corpus summary

| Corpus | Observations | Finite upper | Unbounded upper | Exact finite upper | Exact lower | Mean finite upper gap | Mean lower gap |
|---|---:|---:|---:|---:|---:|---:|---:|
| Full test suite | 489,942 | 480,486 (98.07%) | 9,456 (1.93%) | 361,701 (75.28%) | 239,530 (48.89%) | 1.567e59 | 13.336 |
| Canonical random corpus | 1,000 | 1,000 (100.00%) | 0 | 343 (34.30%) | 232 (23.20%) | 1,588,939.079 | 3.689 |

The full-suite upper-gap mean is dominated by a small number of nested permutation/n-queens iterations whose independent per-level cardinality products compound. The bucket distributions below are more representative than that mean.

## Full test suite distributions

### Finite upper additive overestimate

| Gap | Count | Share |
|---|---:|---:|
| 0 | 361,701 | 75.28% |
| 1 | 23,070 | 4.80% |
| 2–3 | 24,031 | 5.00% |
| 4–7 | 5,440 | 1.13% |
| 8–15 | 4,606 | 0.96% |
| 16–31 | 1,566 | 0.33% |
| 32–63 | 13,042 | 2.71% |
| 64–255 | 10,235 | 2.13% |
| 256+ | 36,795 | 7.66% |

### Finite upper multiplicative overestimate

| Factor | Count | Share |
|---|---:|---:|
| Exact | 361,701 | 75.28% |
| ≤1.25× | 30,465 | 6.34% |
| ≤1.5× | 3,743 | 0.78% |
| ≤2× | 15,510 | 3.23% |
| ≤4× | 15,026 | 3.13% |
| ≤10× | 6,282 | 1.31% |
| >10× | 23,981 | 4.99% |
| Zero result, positive bound | 23,778 | 4.95% |

### Lower additive underestimate

| Gap | Count | Share |
|---|---:|---:|
| 0 | 239,530 | 48.89% |
| 1 | 23,534 | 4.80% |
| 2–3 | 87,189 | 17.80% |
| 4–7 | 95,207 | 19.43% |
| 8–15 | 19,214 | 3.92% |
| 16–31 | 6,919 | 1.41% |
| 32–63 | 2,432 | 0.50% |
| 64–255 | 12,968 | 2.66% |
| 256+ | 2,949 | 0.60% |

### Lower coverage of the actual result

| Coverage | Count | Share |
|---|---:|---:|
| Exact | 239,530 | 48.89% |
| ≥75% | 28,701 | 5.86% |
| ≥50% | 12,915 | 2.64% |
| ≥25% | 72,671 | 14.83% |
| >0% | 87,581 | 17.88% |
| 0% | 48,544 | 9.91% |

## Random corpus distributions

The canonical corpus uses `SpaceFuzzerCorpus.generate(1000, 20260708L, maxDepth = 5, maxResult = 400)`.

### Finite upper additive overestimate

| Gap | Count | Share |
|---|---:|---:|
| 0 | 347 | 34.70% |
| 1 | 129 | 12.90% |
| 2–3 | 139 | 13.90% |
| 4–7 | 117 | 11.70% |
| 8–15 | 88 | 8.80% |
| 16–31 | 55 | 5.50% |
| 32–63 | 43 | 4.30% |
| 64–255 | 50 | 5.00% |
| 256+ | 32 | 3.20% |

### Finite upper multiplicative overestimate

| Factor | Count | Share |
|---|---:|---:|
| Exact | 347 | 34.70% |
| ≤1.25× | 36 | 3.60% |
| ≤1.5× | 70 | 7.00% |
| ≤2× | 125 | 12.50% |
| ≤4× | 158 | 15.80% |
| ≤10× | 140 | 14.00% |
| >10× | 124 | 12.40% |
| Zero result, positive bound | 0 | 0.00% |

### Lower additive underestimate

| Gap | Count | Share |
|---|---:|---:|
| 0 | 233 | 23.30% |
| 1 | 352 | 35.20% |
| 2–3 | 215 | 21.50% |
| 4–7 | 109 | 10.90% |
| 8–15 | 52 | 5.20% |
| 16–31 | 19 | 1.90% |
| 32–63 | 11 | 1.10% |
| 64–255 | 9 | 0.90% |
| 256+ | 0 | 0.00% |

### Lower coverage of the actual result

| Coverage | Count | Share |
|---|---:|---:|
| Exact | 233 | 23.30% |
| ≥75% | 12 | 1.20% |
| ≥50% | 62 | 6.20% |
| ≥25% | 66 | 6.60% |
| >0% | 39 | 3.90% |
| 0% | 588 | 58.80% |

## Least-tight bounds

### Full test suite

- Least-tight upper bounds with no finite ceiling occurred in closure-heavy and fixpoint programs: the largest observed concrete result among these was 244 paths versus `∞`.
- The largest finite upper gap was a nested n-queens iteration with 2 actual paths and upper bound `45,876,906,032,485,984,041,672,329,027,403,720,154,355,271,888,099,553,827,762,194,788,406,957,948,534,784`.
- The next family also had 2 actual paths and upper bound `143,598,679,488,117,255,059,458,196,380,724,250,429,924,690,414,657,046,315,008`.
- The least-tight lower bound had 178,098 actual paths and lower bound zero. The next had 162,606 actual paths and lower bound zero.

### Canonical random corpus

- Every upper bound was finite; the operation laws removed all 37 baseline infinities.
- The largest finite upper gap now has 12 actual paths and upper bound `11,943,936`. It is a deeply nested iteration/subtraction program whose remaining dependent upper products compound.
- The next has 70 actual paths and upper bound `810,006`.
- The least-tight lower bound had 256 actual paths and lower bound 15 (gap 241), from a literal-headed iteration producing `x × (x ∪ x)` followed by singleton subtraction.
- The next lower cases were 99 versus 9 and 97 versus 14.

Z3 closes the repeated Boolean-operand gap: exhaustive tests make `x ∪ (x ∩ y)` and `x ∩ (x ∪ y)` exactly `|x|`, preserve `x ∩ (x ∩ y)` as the inner intersection, and bound `(x ∪ y) \ x` by `|y|`. The operation laws additionally recover nonempty guards, binder-independent iteration, injective unwrap ceilings, and closure members. The main remaining opportunities are correlated iteration groups and iteration bodies whose outputs collide heavily. General products and nested dependent iterations are sound but intentionally assume independence for their upper ceilings.
