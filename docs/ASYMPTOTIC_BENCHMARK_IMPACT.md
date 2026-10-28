# Asymptotic Trie-Layer Benchmark Impact

Measured on 2026-08-08 with OpenJDK, Scala CLI 3.8.1 in Scala 3.3 source mode,
`-Xmx1536m -Xss64m`, and each report in a fresh JVM. The checked-in benchmark
reports present before this sweep are the timing baseline. Ratios below are
`baseline / current`: values above 1 mean the changed implementation is faster.

All eight non-long benchmark entry points completed. The explicitly long
`constantFoldExecutorReport` was excluded as requested. The spatial cost
correlation and exact-counter reports also completed after the timing sweep.
The generated current reports are:

- [TRIE_BENCHMARKS.md](TRIE_BENCHMARKS.md)
- [ZIPPER_ALGEBRA_BENCHMARKS.md](ZIPPER_ALGEBRA_BENCHMARKS.md)
- [ZIPPER_ITER_RANGE_MICRO.md](ZIPPER_ITER_RANGE_MICRO.md)
- [ZIPPER_LARGE_BENCHMARKS.md](ZIPPER_LARGE_BENCHMARKS.md)

The first complete run exposed an unbounded weak aggregate-cache working set and
ran out of a 1.5 GiB heap in Game of Life. The final implementation compacts dead
weak entries without doubling and does not cache maps of at most eight entries:
their bounded scan is constant time. The final full report completes without an
OOM. This specialization reduced the full-report wall time from about 133 seconds
to about 65 seconds while retaining the exact wide-map work laws below.

## Exact asymptotic work

For a union of two width-`W` root maps, the measured work is not a worst-case
over-approximation; it follows the actual Patricia-map distribution exactly.

| W | regime | trie-node visits | Patricia visits | allocations | ns/union |
|---:|---|---:|---:|---:|---:|
| 256 | identity | 1 | 0 | 0 | 108.2 |
| 256 | root-disjoint | 1 | 1 | 1 | 771.5 |
| 256 | mixed quarter | 1 | 129 | 1 | 17,337.2 |
| 256 | interwoven | 1 | 511 | 1 | 48,310.4 |
| 1,024 | identity | 1 | 0 | 0 | 29.9 |
| 1,024 | root-disjoint | 1 | 1 | 1 | 172.5 |
| 1,024 | mixed quarter | 1 | 513 | 1 | 43,261.7 |
| 1,024 | interwoven | 1 | 2,047 | 1 | 192,461.8 |
| 4,096 | identity | 1 | 0 | 0 | 30.6 |
| 4,096 | root-disjoint | 1 | 1 | 1 | 186.2 |
| 4,096 | mixed quarter | 1 | 2,049 | 1 | 213,737.6 |
| 4,096 | interwoven | 1 | 8,191 | 1 | 824,439.5 |
| 16,384 | identity | 1 | 0 | 0 | 46.9 |
| 16,384 | root-disjoint | 1 | 1 | 1 | 169.3 |
| 16,384 | mixed quarter | 1 | 8,193 | 1 | 851,302.1 |
| 16,384 | interwoven | 1 | 32,767 | 1 | 3,485,841.2 |

Thus identity is exactly zero Patricia work, root-disjoint is exactly one visit,
mixed-quarter is `W/2 + 1`, and fully interwoven is `2W - 1`. All four cases
perform one trie-node visit; only the non-identity cases allocate one result
parent. A disjoint wide intersection likewise uses one trie-node and one
Patricia visit.

Other exact scaling checks also pass:

- single-path repeated and periodic suffix closures perform zero generic trie
  visits and at most `4D` allocations;
- cursor descent performs one node visit for depth `D`;
- focused zipper reconstruction performs exactly `D` allocations and no node
  scans;
- a width-`W` ordered sibling walk sorts once and then moves adjacently;
- a 12,000-factor left-associated concatenation completes linearly and without
  recursive prefix copying;
- bulk wide construction allocates exactly `W + 1` nodes, deep construction
  exactly `W - 1`, and joining `W` identical references allocates and visits
  nothing.

## Dedicated trie algebra timings

This older benchmark has four fixed distributions. It confirms the intended
classes, but also exposes substantial constant-factor regressions in the new
metadata path. In particular, disjoint subtraction remains constant with size
but rises from 4–10 ns to 47–114 ns; restriction remains linear but is 6–9 times
slower than the baseline.

| operation | size | baseline ns | current ns | baseline/current |
|---|---:|---:|---:|---:|
| union-subset | 1,024 | 10,760.3 | 11,752.8 | 0.92x |
| union-subset | 4,096 | 27,915.4 | 35,119.1 | 0.79x |
| union-subset | 16,384 | 105,026.1 | 115,000.0 | 0.91x |
| union-subset | 65,536 | 325,948.0 | 508,380.3 | 0.64x |
| intersection-subset | 1,024 | 5,146.6 | 7,135.9 | 0.72x |
| intersection-subset | 4,096 | 30,715.5 | 35,709.6 | 0.86x |
| intersection-subset | 16,384 | 138,041.7 | 73,575.6 | 1.88x |
| intersection-subset | 65,536 | 357,807.3 | 494,067.8 | 0.72x |
| restriction-quarter | 1,024 | 6,780.3 | 49,515.3 | 0.14x |
| restriction-quarter | 4,096 | 29,647.1 | 193,536.5 | 0.15x |
| restriction-quarter | 16,384 | 116,578.1 | 699,367.2 | 0.17x |
| restriction-quarter | 65,536 | 488,312.5 | 4,468,260.4 | 0.11x |
| subtraction-disjoint | 1,024 | 9.9 | 91.2 | 0.11x |
| subtraction-disjoint | 4,096 | 8.2 | 46.8 | 0.18x |
| subtraction-disjoint | 16,384 | 4.1 | 48.3 | 0.08x |
| subtraction-disjoint | 65,536 | 4.1 | 113.7 | 0.04x |

The 64-fold width increase changes current time by 43.3x for subset union,
69.2x for subset intersection, 90.2x for quarter restriction, and only 1.25x
for disjoint subtraction. These are measured scaling ratios, not claimed upper
bounds.

## Construction

| paths | baseline wide ms | current wide ms | ratio | baseline deep ms | current deep ms | ratio |
|---:|---:|---:|---:|---:|---:|---:|
| 256 | 0.126 | 0.639 | 0.20x | 0.828 | 0.294 | 2.82x |
| 1,024 | 0.095 | 0.708 | 0.13x | 0.990 | 0.500 | 1.98x |
| 4,096 | 0.298 | 2.172 | 0.14x | 0.900 | 4.881 | 0.18x |
| 16,384 | 0.799 | 4.663 | 0.17x | 3.216 | 5.643 | 0.57x |

The aggregate-aware bulk builder is still 198x faster at width 16,384 than the
921.833 ms review baseline that repeatedly rebuilt persistent parents. Against
the immediately preceding bulk-builder timing, however, wide construction is
5–7x slower and deep construction is mixed. Exact allocation counts confirm
that the quadratic reconstruction has not returned.

## Independent product to union

The optimized expression retains a large advantage over the definition-level
form. The current optimized runtime is better in two rows and worse in two; the
relative headline improves mostly because the unoptimized source grows more
quickly, so it must not be read as an across-the-board optimized-runtime win.

| heads | paths | baseline optimized ms | current optimized ms | ratio | current source/optimized | current compiled execT ms |
|---:|---:|---:|---:|---:|---:|---:|
| 32 | 64 | 0.2598 | 0.2040 | 1.27x | 13.63x | 0.3718 |
| 64 | 128 | 0.0969 | 0.1453 | 0.67x | 16.22x | 0.2743 |
| 128 | 256 | 0.2888 | 0.2595 | 1.11x | 48.83x | 0.4967 |
| 256 | 512 | 0.2124 | 0.3507 | 0.61x | 80.46x | 0.7001 |

## Historical pre-SCC cornerstone runtime comparison

This table is the complete old/new comparison for the program set measured in
the 2026-08-08 trie-layer sweep. Both snapshots predate any SCC
cornerstone, so this is a frozen historical comparison rather than a current
inventory of cornerstone programs. The current generated
[trie](TRIE_BENCHMARKS.md) and
[large-zipper](ZIPPER_LARGE_BENCHMARKS.md) reports include the SCC row.

Every runtime row measured in that historical sweep is included below for the
affected trie, zipper, and compiled-trie backends. Times are milliseconds. The
ratio column is baseline/current. Rows at the report's 0.001 ms timer floor
should be treated as equality, not a resolved speed difference.

| benchmark | evalTrie old → new | ratio | evalZ old → new | ratio | execT old → new | ratio |
|---|---:|---:|---:|---:|---:|---:|
| aunt — reference | 0.404 → 0.395 | 1.02x | 0.757 → 1.164 | 0.65x | 0.449 → 0.308 | 1.46x |
| aunt — process-sc static family | 0.558 → 0.605 | 0.92x | 1.169 → 0.550 | 2.13x | 0.243 → 0.342 | 0.71x |
| aunt synthetic — reference 60 people | 1.304 → 1.619 | 0.81x | 2.873 → 2.240 | 1.28x | 1.365 → 1.433 | 0.95x |
| aunt royal92 — reference fallback | 0.112 → 0.092 | 1.22x | 0.133 → 0.145 | 0.92x | 0.105 → 0.080 | 1.31x |
| aunt synthetic — process-sc 24 people | 2.061 → 1.102 | 1.87x | 1.217 → 1.228 | 0.99x | 0.149 → 0.287 | 0.52x |
| graph two-hop — 90-chain | 0.839 → 1.650 | 0.51x | 15.892 → 16.707 | 0.95x | 0.313 → 1.511 | 0.21x |
| graph mutual — 90-chain | 0.256 → 0.196 | 1.31x | 1.096 → 0.921 | 1.19x | 0.160 → 0.182 | 0.88x |
| datalog semi-naive — source 24-chain | 6.232 → 8.469 | 0.74x | n/a | n/a | 0.002 → 0.004 | timer floor |
| datalog semi-naive — process-sc 24-chain | 4.379 → 9.469 | 0.46x | n/a | n/a | 1.759 → 3.086 | 0.57x |
| life — source random 24x24 | 559.616 → 365.660 | 1.53x | 606.670 → 389.393 | 1.56x | 2.086 → 4.372 | 0.48x |
| life — compile-pass random 24x24 | 958.434 → 264.429 | 3.62x | 794.734 → 282.948 | 2.81x | 0.001 → 0.001 | timer floor |
| life — compile-pass initial literal | 0.117 → 0.029 | 4.03x | 0.111 → 0.030 | 3.70x | 0.001 → 0.001 | timer floor |
| temperature — NOAA slice | 0.028 → 0.009 | 3.11x | 0.053 → 0.030 | 1.77x | 0.012 → 0.006 | 2.00x |
| temperature — synthetic 32x64 | 0.023 → 0.052 | 0.44x | 0.094 → 0.051 | 1.84x | 0.006 → 0.020 | 0.30x |
| puzzle — 2x2 source | 5.007 → 6.634 | 0.75x | 9.779 → 12.396 | 0.79x | 0.001 → 0.001 | timer floor |
| puzzle — 2x2 compile-pass | 0.005 → 0.006 | 0.83x | 0.009 → 0.007 | 1.29x | 0.001 → 0.001 | timer floor |
| puzzle — 3x3 source depth 8 | 409.636 → 517.448 | 0.79x | n/a | n/a | 0.001 → 0.001 | timer floor |
| puzzle — 3x3 compile-pass depth 8 | 0.214 → 0.284 | 0.75x | 0.220 → 0.625 | 0.35x | 0.001 → 0.001 | timer floor |
| puzzle — 4x4 source depth 5 | 694.371 → 954.730 | 0.73x | n/a | n/a | 0.001 → 0.001 | timer floor |
| n-queens — 8x8 source | 1,487.658 → 2,112.835 | 0.70x | n/a | n/a | 0.001 → 0.001 | timer floor |
| n-queens — 8x8 compile-pass | 0.039 → 0.053 | 0.74x | 0.039 → 0.049 | 0.80x | 0.001 → 0.001 | timer floor |

For rows where both measurements are at least 0.01 ms, the geometric-mean
baseline/current factors are 0.978x across 19 evalTrie rows, 1.226x across 15
evalZ rows, and 0.685x across 9 execT rows. This is a 2.2% evalTrie regression,
22.6% evalZ improvement, and 31.5% execT regression in this one sweep. The
per-row spread is much larger than those aggregates.

### Historical pre-SCC compilation comparison

Compilation is not the target of the trie-layer changes, but the historical
sweep timed it, so every total from that pre-SCC program set is included. These
single-shot values are especially sensitive to JIT and GC state.

| benchmark | total compile ms old → new | ratio |
|---|---:|---:|
| aunt — reference | 2.958 → 2.649 | 1.12x |
| aunt — process-sc | 59.454 → 59.281 | 1.00x |
| aunt synthetic — reference | 1.775 → 1.548 | 1.15x |
| aunt royal92 | 1.458 → 1.333 | 1.09x |
| aunt synthetic — process-sc | 12.827 → 14.626 | 0.88x |
| graph two-hop | 1.610 → 1.504 | 1.07x |
| graph mutual | 1.385 → 1.325 | 1.05x |
| datalog — source | 16.831 → 27.161 | 0.62x |
| datalog — process-sc | 92.140 → 102.190 | 0.90x |
| life — source | 3,195.464 → 3,752.392 | 0.85x |
| life — compile-pass | 162.621 → 126.589 | 1.28x |
| life — initial literal | 80.829 → 104.103 | 0.78x |
| temperature — NOAA | 0.950 → 0.419 | 2.27x |
| temperature — synthetic | 0.500 → 0.182 | 2.75x |
| puzzle — 2x2 source | 3.192 → 3.421 | 0.93x |
| puzzle — 2x2 compile-pass | 11.693 → 15.759 | 0.74x |
| puzzle — 3x3 source | 44.545 → 42.851 | 1.04x |
| puzzle — 3x3 compile-pass | 120.572 → 119.237 | 1.01x |
| puzzle — 4x4 source | 61.056 → 66.391 | 0.92x |
| n-queens — source | 350.722 → 390.155 | 0.90x |
| n-queens — compile-pass | 395.998 → 479.045 | 0.83x |

## Zipper algebra: all data distributions

The following compact table covers all 66 rows. Each cell is
`evalTrie factor / evalZ factor` at the named physical sharing percentage.

| group | operation | 1% shared | 50% shared | 90% shared |
|---|---|---:|---:|---:|
| binary | union | 0.24x / 0.31x | 0.19x / 0.16x | 0.25x / 0.25x |
| binary | intersection | 0.17x / 0.20x | 0.20x / 0.22x | 0.46x / 0.58x |
| binary | subtraction | 0.17x / 0.45x | 1.98x / 1.96x | 0.54x / 0.52x |
| binary | restriction | 0.36x / 0.43x | 1.91x / 1.57x | 0.66x / 0.68x |
| binary | raffination | 0.74x / 0.25x | 0.94x / 1.01x | 0.31x / 0.26x |
| binary | composition | 1.11x / 0.27x | 1.12x / 2.64x | 1.19x / 0.94x |
| n-ary | three-way intersection | 0.12x / 0.36x | 0.23x / 0.72x | 0.79x / 1.19x |
| unary | wrap | 0.88x / 1.20x | 0.75x / 0.80x | 0.67x / 0.75x |
| unary | unwrap | 0.80x / 0.88x | 0.75x / 1.25x | 0.67x / 0.67x |
| unary | tails-union | 0.33x / 0.18x | 0.09x / 0.20x | 0.21x / 0.29x |
| unary | tails-intersection | 0.23x / 0.18x | 1.44x / 0.67x | 0.96x / 1.00x |
| unary | prefix-closure | 0.50x / 0.36x | 0.24x / 0.48x | 0.46x / 0.44x |
| unary | suffix-closure | 1.95x / 0.29x | 0.36x / 0.34x | 0.39x / 0.27x |
| unary | tails-closure | 0.36x / 0.31x | 0.35x / 0.30x | 0.48x / 0.39x |
| range | first(512) | 1.11x / 1.25x | 0.77x / 0.89x | 0.80x / 0.83x |
| range | last(512) | 1.90x / 1.10x | 0.67x / 1.00x | 0.73x / 0.54x |
| combination | union then exact intersection | 0.24x / 0.30x | 0.18x / 0.19x | 0.26x / 3.54x |
| combination | diff then restriction | 0.45x / 1.54x | 0.39x / 0.58x | 0.64x / 0.47x |
| combination | product exact intersection | 1.97x / 0.49x | 1.77x / 0.69x | 1.18x / 0.72x |
| combination | product prefix restriction | 1.43x / 0.45x | 1.31x / 0.51x | 0.80x / 0.79x |
| combination | tails of restricted union | 0.52x / 1.00x | 0.20x / 0.27x | 0.52x / 0.33x |
| combination | range of union | 0.18x / 1.21x | 0.10x / 0.51x | 0.38x / 0.91x |

Across these 66 rows, the geometric-mean factors are 0.510x for evalTrie and
0.545x for evalZ; 14 trie rows and 13 zipper rows are faster. This is the clearest
remaining regression signal. The exact laws improved, but aggregate propagation
and wrapper/frontier materialization still carry high constants on physically
large aligned tries. This result should block any claim of an across-the-board
performance improvement.

## Range-tail microbenchmark

| source heads | previous implementation ms | current implementation ms | previous/current | old algorithm emulation ms | old/current now |
|---:|---:|---:|---:|---:|---:|
| 32 | 6.497 | 6.293 | 1.03x | 6.093 | 0.97x |
| 96 | 28.257 | 25.392 | 1.11x | 25.906 | 1.02x |
| 192 | 113.601 | 99.932 | 1.14x | 133.530 | 1.34x |

The new one-pass per-key accumulation is increasingly useful at the largest
measured head count, but at 32 heads its bookkeeping is indistinguishable from
the old algorithm.

## Large selective zipper programs

| benchmark | size | evalTrie old → new | evalZ old → new |
|---|---|---:|---:|
| product exact intersection | 2,000² | 2.203 → 1.832 (1.20x) | 1.125 → 1.801 (0.62x) |
| product exact intersection | 10,000² | 3.889 → 2.544 (1.53x) | 6.453 → 2.433 (2.65x) |
| product exact intersection | 30,000² | 10.218 → 4.919 (2.08x) | 4.023 → 4.262 (0.94x) |
| product prefix restriction | 2,000² | 0.416 → 0.624 (0.67x) | 0.277 → 0.533 (0.52x) |
| product prefix restriction | 10,000² | 2.812 → 1.578 (1.78x) | 1.223 → 1.479 (0.83x) |
| product prefix restriction | 30,000² | 10.442 → 17.306 (0.60x) | 4.058 → 8.813 (0.46x) |
| aunt query | 2,720 facts | 0.173 → 0.121 (1.43x) | 0.142 → 0.335 (0.42x) |
| aunt query | 6,720 facts | 0.085 → 0.175 (0.49x) | 0.126 → 0.236 (0.53x) |
| semi-naive datalog | 40 nodes | 21.272 → 31.520 (0.67x) | unsupported |
| semi-naive datalog | 80 nodes | 94.599 → 110.226 (0.86x) | unsupported |

Exact-product intersection improves for evalTrie at all three sizes and for
evalZ at 10,000². Prefix restriction is mixed at 10,000² and regresses sharply
at 30,000². Recursive zipper datalog remains explicitly unsupported rather than
silently falling back to materialization.

## Spatial cost validation

The exact-counter report emitted 63 backend/case rows and completed without a
bound failure. Spearman correlations between annotated cost and measured time
were 1.000 for Reference, 1.000 for Trie, 0.800 for Zipper, and 1.000 for Graph.
These are validation signals for the abstract cost model, not replacements for
the concrete timing and exact visit results above.

## Bottom line

The changes succeed on the make-or-break asymptotic cases: disjoint Patricia
branches, identity, cursor depth, zipper rebuild depth, left-associated path
flattening, construction allocation count, and single-path closure are now
measured in their exact distribution-sensitive classes. They also prevent the
benchmark-scale aggregate-cache OOM.

They do **not** yet constitute a wall-time win across the suite. Whole-program
evalTrie is approximately flat in aggregate and evalZ improves, but execT and
the broad physical-sharing zipper matrix regress materially. Restriction,
tails-union/closure, and large prefix-selective products are the clearest next
targets. The current evidence supports keeping the asymptotic structure while
reducing metadata/cache and frontier-materialization constants; it does not
support reverting to width scans or claiming universal speedups.
