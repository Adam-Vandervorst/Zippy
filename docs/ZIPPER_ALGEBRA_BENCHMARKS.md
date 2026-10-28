# Zipper Algebra Sharing Benchmarks

This report isolates direct zipper evaluation over physically large tries. Each scenario builds two full operands `a` and `b` with the same top-level keys, plus a sparse third operand `cOverlap` containing only the buckets that are physically shared by all three. For the requested sharing level, the corresponding child subtries are the same JVM objects in all overlapping operands; the rest of `a` and `b` have the same outer shape but distinct unique leaves. Each child subtrie also has a small common tail vocabulary so `tailsIntersection` and ordinary intersections have non-empty work to do outside the physically shared portion.

Each operand has 1500 top-level buckets and 16 paths per bucket. Timings compare `evalTrie(expr).pathCount` to `evalZ(expr).pathCount` after an untimed correctness check and warmup. Each backend is adaptively batched by doubling from one invocation until a batch reaches 10 ms or 4,096 invocations, then the table reports the median per-invocation time from seven batches. This bounds total measurement work while preventing one noisy invocation from defining a row. Very large results are checked by path count plus border membership samples instead of decoding every path.

| target shared nodes | shared top-level subtries | measured shared nodes / operand nodes | `a`/`b` paths | `a`/`b` trie nodes | sparse third paths | prefix paths |
|---:|---:|---:|---:|---:|---:|---:|
| 1% | 15 / 1,500 | 1.00% | 24,000 | 31,501 | 240 | 96 |
| 50% | 750 / 1,500 | 50.00% | 24,000 | 31,501 | 12,000 | 96 |
| 90% | 1,350 / 1,500 | 90.00% | 24,000 | 31,501 | 21,600 | 96 |

| share | group | operation | result paths | result trie nodes | evalTrie ms | evalZ ms | evalTrie / evalZ | note |
|---:|---|---|---:|---:|---:|---:|---:|---|
| 1% | binary | union | 41,820 | 53,776 | 5.289 | 3.941 | 1.34 x | merge two aligned huge tries |
| 1% | binary | intersection | 6,180 | 9,226 | 1.391 | 1.925 | 0.72 x | walk only common child keys |
| 1% | binary | subtraction | 17,820 | 23,761 | 2.592 | 1.642 | 1.58 x | left-guided traversal |
| 1% | binary | restriction | 1,536 | 2,017 | 0.036 | 0.036 | 1.00 x | top-level prefix filter |
| 1% | binary | raffination | 22,464 | 29,485 | 0.251 | 0.150 | 1.67 x | complement of the prefix filter |
| 1% | binary | composition | 576,000,000 | 756,031,501 | 8.272 | 8.093 | 1.02 x | no selective consumer; full product is materialized |
| 1% | n-ary | three-way intersection | 240 | 316 | 3.041 | 0.003 | 1208.92 x | evalZ flattens nested intersections and starts from the sparse overlap operand |
| 1% | unary | wrap | 24,000 | 31,502 | 0.000 | 0.001 | 0.57 x | virtual prefix node |
| 1% | unary | unwrap | 24,000 | 31,501 | 0.000 | 0.000 | 1.02 x | descend through virtual prefix |
| 1% | unary | tails-union | 18,004 | 22,506 | 2.952 | 3.468 | 0.85 x | join every first-level tail |
| 1% | unary | tails-intersection | 4 | 6 | 0.612 | 0.477 | 1.28 x | meet every first-level tail |
| 1% | unary | prefix-closure | 31,500 | 31,501 | 3.646 | 3.678 | 0.99 x | all non-empty prefixes |
| 1% | unary | suffix-closure | 48,008 | 60,010 | 17.126 | 17.954 | 0.95 x | all non-empty suffixes |
| 1% | unary | tails-closure | 48,009 | 60,010 | 19.488 | 11.673 | 1.67 x | epsilon plus suffix closure |
| 1% | range | first(512) | 512 | 673 | 0.004 | 0.005 | 0.80 x | ordered border slice |
| 1% | range | last(512) | 512 | 673 | 0.005 | 0.006 | 0.88 x | ordered border slice |
| 1% | combination | union then exact intersection | 1 | 4 | 2.738 | 0.002 | 1158.48 x | selective consumer over a virtual union |
| 1% | combination | diff then restriction | 1,140 | 1,521 | 1.231 | 0.073 | 16.95 x | left-guided diff under prefix filter |
| 1% | combination | product exact intersection | 1 | 7 | 8.687 | 0.006 | 1397.01 x | selector should avoid the full product |
| 1% | combination | product prefix restriction | 24,000 | 31,504 | 8.322 | 0.001 | 6188.92 x | one product row selected by prefix |
| 1% | combination | tails of restricted union | 2,296 | 2,871 | 3.258 | 0.342 | 9.53 x | join tails after a logical prefix filter |
| 1% | combination | range of union | 512 | 666 | 2.976 | 0.555 | 5.36 x | border slice over a virtual union |
| 50% | binary | union | 33,000 | 42,751 | 1.220 | 1.228 | 0.99 x | merge two aligned huge tries |
| 50% | binary | intersection | 15,000 | 20,251 | 0.595 | 0.611 | 0.97 x | walk only common child keys |
| 50% | binary | subtraction | 9,000 | 12,001 | 0.536 | 0.547 | 0.98 x | left-guided traversal |
| 50% | binary | restriction | 1,536 | 2,017 | 0.021 | 0.022 | 0.97 x | top-level prefix filter |
| 50% | binary | raffination | 22,464 | 29,485 | 0.180 | 0.167 | 1.08 x | complement of the prefix filter |
| 50% | binary | composition | 576,000,000 | 756,031,501 | 8.486 | 8.457 | 1.00 x | no selective consumer; full product is materialized |
| 50% | n-ary | three-way intersection | 12,000 | 15,751 | 0.665 | 0.020 | 34.02 x | evalZ flattens nested intersections and starts from the sparse overlap operand |
| 50% | unary | wrap | 24,000 | 31,502 | 0.000 | 0.000 | 0.75 x | virtual prefix node |
| 50% | unary | unwrap | 24,000 | 31,501 | 0.000 | 0.000 | 0.72 x | descend through virtual prefix |
| 50% | unary | tails-union | 18,004 | 22,506 | 3.020 | 3.355 | 0.90 x | join every first-level tail |
| 50% | unary | tails-intersection | 4 | 6 | 0.465 | 0.465 | 1.00 x | meet every first-level tail |
| 50% | unary | prefix-closure | 31,500 | 31,501 | 4.002 | 3.899 | 1.03 x | all non-empty prefixes |
| 50% | unary | suffix-closure | 48,008 | 60,010 | 12.447 | 13.218 | 0.94 x | all non-empty suffixes |
| 50% | unary | tails-closure | 48,009 | 60,010 | 10.980 | 11.513 | 0.95 x | epsilon plus suffix closure |
| 50% | range | first(512) | 512 | 673 | 0.005 | 0.006 | 0.91 x | ordered border slice |
| 50% | range | last(512) | 512 | 673 | 0.006 | 0.007 | 0.93 x | ordered border slice |
| 50% | combination | union then exact intersection | 1 | 4 | 1.391 | 0.001 | 1410.29 x | selective consumer over a virtual union |
| 50% | combination | diff then restriction | 552 | 737 | 0.571 | 0.047 | 12.12 x | left-guided diff under prefix filter |
| 50% | combination | product exact intersection | 1 | 7 | 8.220 | 0.005 | 1677.04 x | selector should avoid the full product |
| 50% | combination | product prefix restriction | 24,000 | 31,504 | 8.088 | 0.001 | 5937.66 x | one product row selected by prefix |
| 50% | combination | tails of restricted union | 1,708 | 2,136 | 1.581 | 0.261 | 6.05 x | join tails after a logical prefix filter |
| 50% | combination | range of union | 512 | 673 | 1.356 | 0.405 | 3.35 x | border slice over a virtual union |
| 90% | binary | union | 25,800 | 33,751 | 0.205 | 0.204 | 1.01 x | merge two aligned huge tries |
| 90% | binary | intersection | 22,200 | 29,251 | 0.108 | 0.110 | 0.98 x | walk only common child keys |
| 90% | binary | subtraction | 1,800 | 2,401 | 0.080 | 0.080 | 0.99 x | left-guided traversal |
| 90% | binary | restriction | 1,536 | 2,017 | 0.022 | 0.035 | 0.63 x | top-level prefix filter |
| 90% | binary | raffination | 22,464 | 29,485 | 0.253 | 0.200 | 1.27 x | complement of the prefix filter |
| 90% | binary | composition | 576,000,000 | 756,031,501 | 8.162 | 8.144 | 1.00 x | no selective consumer; full product is materialized |
| 90% | n-ary | three-way intersection | 21,600 | 28,351 | 0.133 | 0.034 | 3.87 x | evalZ flattens nested intersections and starts from the sparse overlap operand |
| 90% | unary | wrap | 24,000 | 31,502 | 0.000 | 0.000 | 0.73 x | virtual prefix node |
| 90% | unary | unwrap | 24,000 | 31,501 | 0.000 | 0.000 | 0.95 x | descend through virtual prefix |
| 90% | unary | tails-union | 18,004 | 22,506 | 3.162 | 3.438 | 0.92 x | join every first-level tail |
| 90% | unary | tails-intersection | 4 | 6 | 0.458 | 0.459 | 1.00 x | meet every first-level tail |
| 90% | unary | prefix-closure | 31,500 | 31,501 | 4.086 | 4.126 | 0.99 x | all non-empty prefixes |
| 90% | unary | suffix-closure | 48,008 | 60,010 | 13.107 | 12.103 | 1.08 x | all non-empty suffixes |
| 90% | unary | tails-closure | 48,009 | 60,010 | 11.903 | 12.175 | 0.98 x | epsilon plus suffix closure |
| 90% | range | first(512) | 512 | 673 | 0.005 | 0.005 | 0.90 x | ordered border slice |
| 90% | range | last(512) | 512 | 673 | 0.006 | 0.006 | 0.91 x | ordered border slice |
| 90% | combination | union then exact intersection | 1 | 4 | 0.224 | 0.001 | 226.98 x | selective consumer over a virtual union |
| 90% | combination | diff then restriction | 72 | 97 | 0.084 | 0.026 | 3.21 x | left-guided diff under prefix filter |
| 90% | combination | product exact intersection | 1 | 7 | 8.382 | 0.005 | 1709.41 x | selector should avoid the full product |
| 90% | combination | product prefix restriction | 24,000 | 31,504 | 8.485 | 0.001 | 6258.01 x | one product row selected by prefix |
| 90% | combination | tails of restricted union | 1,228 | 1,536 | 0.375 | 0.184 | 2.04 x | join tails after a logical prefix filter |
| 90% | combination | range of union | 512 | 673 | 0.299 | 0.381 | 0.78 x | border slice over a virtual union |

Ratios above `1.00 x` mean the zipper evaluator is faster. Direct `composition` intentionally has no selective consumer, so it is a useful overhead baseline rather than the expected zipper win. Selective product rows exercise composition without forcing the full product before the final materialization boundary.
