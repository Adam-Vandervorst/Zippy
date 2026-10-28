# Review 6 response

Both findings in `review.md` are addressed and have permanent executable gates.

## 1. Incremental union and fixpoint accumulation

The reviewed parent-width scan had already been removed from `TrieSpace.unionResult`,
but one quadratic mechanism remained below it: aggregate summaries for Patricia
subbranches were operation-local. After an update, only the result root summary
survived. The next singleton union therefore rediscovered aggregates for unchanged
sibling branches, which recreated result-width work inside the Patricia layer.

`TrieIntMapOps.withAggregateResult` now promotes summaries for persistent map
branches into the weak identity cache at the operation boundary. Obsolete map
versions are weakly held, maps of at most eight entries retain their bounded O(1)
scan, and a batch promotion takes one cache lock. A subsequent update retrieves
unchanged sibling summaries in O(1) and rebuilds only its touched Patricia spine.

The permanent folded-union test checks K singleton operands at K=256/1,024/4,096:

- semantic trie visits are exactly K;
- parent allocations are exactly K−1;
- Patricia visits are bounded by the fixed-width key spine rather than K².

The dedicated benchmark extends this to the review's K values:

| K | trie visits | Patricia visits | allocations | current ms | review ms | speedup |
|---:|---:|---:|---:|---:|---:|---:|
| 512 | 512 | 7,907 | 511 | 1.047 | 6.75 | 6.4x |
| 2,048 | 2,048 | 35,811 | 2,047 | 4.797 | 92.83 | 19.4x |
| 8,192 | 8,192 | 159,715 | 8,191 | 16.059 | 2,567.28 | 159.9x |
| 32,768 | 32,768 | 704,483 | 32,767 | 76.999 | 27,887.09 | 362.2x |

The Patricia series grows by 4.53x, 4.46x, and 4.41x for each 4x increase in K.
That is the measured sequential-key distribution: one increasingly deep touched
spine per delta, not a scan of the accumulator width.

`TrieConstructionAsymptoticTest` also evaluates an actual `Space.Fixpoint` with a
wide accumulator and one new path at widths 256, 1,024, 4,096, and 16,384. It
requires at most eight semantic trie visits, a width-invariant allocation count,
exactly two rounds, and Patricia work below a constant multiple of the fixed
32-bit key depth. Exact visit counts are intentionally not compared across
widths: process-global path-label interning changes the numeric `IntMap` layout
without changing the constant-depth complexity claim. This guards the evaluator
call site, not only direct `TrieSpace.union`.

The existing generated semi-naive datalog benchmark also improves on the final
code: 40 nodes move from 31.520 to 30.667 ms, and 80 nodes from 110.226 to 87.099
ms (1.27x faster at the larger point).

## 2. Patricia visits in the spatial cost model

`SpatialCostComponents` now has five fields matching `ExecutorCostCounts`:

1. `nodeVisits`
2. `patriciaVisits`
3. `pathComparisons`
4. `allocations`
5. `rounds`

The new component participates in sequential addition, iterator/fixpoint scaling,
backend specialization, and recursive-recurrence closing. Trie transfers use the
representation actually traversed:

- head-disjoint boolean operations: one Patricia visit;
- general boolean operations: both operand representations;
- composition: Patricia nodes of the traversed left trie only;
- restriction: prefix-trie nodes plus the source child-map frontiers reached by
  those prefix depths;
- range construction: Patricia nodes of the materialized result.

Zipper inherits the native trie work, and Graph adds dispatch only to semantic
node visits. Reference operations retain zero Patricia work.

The asymmetric counter corpus now gates `patriciaVisits` independently. Every
row requires predicted ≥ actual, and the corpus still requires stability when
an irrelevant operand grows and strict growth when the traversed operand grows.
Unlike the four topology-independent components, Patricia visits do not have a
process-order-independent ≤8× gate: path labels receive process-global numeric
ids, so earlier suites can change the `IntMap` topology and exact visit count.
All 63 optimized-backend rows pass the soundness and asymptotic gates. In the
canonical focused run, prediction/actual ratios range from 1.000 to 7.324 with a
mean of 1.678. Representative rows from that recorded run are:

| case | predicted | actual |
|---|---:|---:|
| restriction-left-64/512/4096 | 8 / 8 / 8 | 6 / 6 / 6 |
| restriction-right-64 | 4,226 | 577 |
| restriction-right-512 | 5,122 | 3,206 |
| restriction-right-4096 | 12,290 | 12,287 |
| intersection-left-4096 | 1 | 1 |
| subtraction-left-4096 | 1 | 1 |
| composition-left-64/256/1024 | 130 / 514 / 2,050 | 127 / 511 / 2,047 |
| composition-right-64/256/1024 | 10 / 10 / 10 | 7 / 7 / 7 |

The documentation now names Patricia work explicitly rather than implying it is
covered by semantic node visits.

## Verification

The following focused suites pass on the final implementation:

- `TrieConstructionAsymptoticTest`
- `TrieLayerAsymptoticTest`
- `TrieSpaceTest`
- `ZipperDenotationOracleTest`
- `SpatialCostCounterTest`
- `SpatialCostCorrelationTest`
- `SpatialTypeTest`

The non-long incremental-union, trie-algebra, and Patricia-distribution reports
also complete. Raw output stays under `/tmp`; `build.log` records summaries only.
