# Zipper Algebra Sharing Benchmarks

This report isolates direct zipper evaluation over physically large tries. Each scenario builds two full operands `a` and `b` with the same top-level keys, plus a sparse third operand `cOverlap` containing only the buckets that are physically shared by all three. For the requested sharing level, the corresponding child subtries are the same JVM objects in all overlapping operands; the rest of `a` and `b` have the same outer shape but distinct unique leaves. Each child subtrie also has a small common tail vocabulary so `tailsIntersection` and ordinary intersections have non-empty work to do outside the physically shared portion.

Each operand has 1500 top-level buckets and 16 paths per bucket. Timings compare `evalTrie(expr).pathCount` to `evalZ(expr).pathCount` after a correctness check. Very large results are checked by path count plus border membership samples instead of decoding every path.

| target shared nodes | shared top-level subtries | measured shared nodes / operand nodes | `a`/`b` paths | `a`/`b` trie nodes | sparse third paths | prefix paths |
|---:|---:|---:|---:|---:|---:|---:|
| 1% | 15 / 1,500 | 1.00% | 24,000 | 31,501 | 240 | 96 |
| 50% | 750 / 1,500 | 50.00% | 24,000 | 31,501 | 12,000 | 96 |
| 90% | 1,350 / 1,500 | 90.00% | 24,000 | 31,501 | 21,600 | 96 |

| share | group | operation | result paths | result trie nodes | evalTrie ms | evalZ ms | evalTrie / evalZ | note |
|---:|---|---|---:|---:|---:|---:|---:|---|
| 1% | binary | union | 41,820 | 53,776 | 4.100 | 0.822 | 4.99 x | merge two aligned huge tries |
| 1% | binary | intersection | 6,180 | 9,226 | 1.360 | 1.414 | 0.96 x | walk only common child keys |
| 1% | binary | subtraction | 17,820 | 23,761 | 2.266 | 2.277 | 0.99 x | left-guided traversal |
| 1% | binary | restriction | 1,536 | 2,017 | 0.080 | 0.089 | 0.91 x | top-level prefix filter |
| 1% | binary | raffination | 22,464 | 29,485 | 0.076 | 0.041 | 1.84 x | complement of the prefix filter |
| 1% | binary | composition | 576,000,000 | 756,031,501 | 12.165 | 5.103 | 2.38 x | no selective consumer; full product is materialized |
| 1% | n-ary | three-way intersection | 240 | 316 | 1.286 | 0.030 | 42.86 x | evalZ flattens nested intersections and starts from the sparse overlap operand |
| 1% | unary | wrap | 24,000 | 31,502 | 0.007 | 0.011 | 0.66 x | virtual prefix node |
| 1% | unary | unwrap | 24,000 | 31,501 | 0.007 | 0.006 | 1.16 x | descend through virtual prefix |
| 1% | unary | tails-union | 18,004 | 22,506 | 3.307 | 1.546 | 2.14 x | join every first-level tail |
| 1% | unary | tails-intersection | 4 | 6 | 1.128 | 0.951 | 1.19 x | meet every first-level tail |
| 1% | unary | prefix-closure | 31,500 | 31,501 | 2.056 | 2.041 | 1.01 x | all non-empty prefixes |
| 1% | unary | suffix-closure | 48,008 | 60,010 | 5.627 | 4.823 | 1.17 x | all non-empty suffixes |
| 1% | unary | tails-closure | 48,009 | 60,010 | 5.757 | 5.453 | 1.06 x | epsilon plus suffix closure |
| 1% | range | first(512) | 512 | 673 | 0.012 | 0.014 | 0.87 x | ordered border slice |
| 1% | range | last(512) | 512 | 673 | 0.172 | 0.131 | 1.31 x | ordered border slice |
| 1% | combination | union then exact intersection | 1 | 4 | 0.783 | 0.835 | 0.94 x | selective consumer over a virtual union |
| 1% | combination | diff then restriction | 1,140 | 1,521 | 0.195 | 0.038 | 5.20 x | left-guided diff under prefix filter |
| 1% | combination | product exact intersection | 1 | 7 | 5.122 | 3.305 | 1.55 x | selector should avoid the full product |
| 1% | combination | product prefix restriction | 24,000 | 31,504 | 4.950 | 2.182 | 2.27 x | one product row selected by prefix |
| 1% | combination | tails of restricted union | 2,296 | 2,871 | 0.522 | 0.211 | 2.47 x | join tails after a logical prefix filter |
| 1% | combination | range of union | 512 | 666 | 0.412 | 0.404 | 1.02 x | border slice over a virtual union |
| 50% | binary | union | 33,000 | 42,751 | 0.178 | 0.176 | 1.01 x | merge two aligned huge tries |
| 50% | binary | intersection | 15,000 | 20,251 | 0.151 | 0.167 | 0.90 x | walk only common child keys |
| 50% | binary | subtraction | 9,000 | 12,001 | 0.871 | 0.870 | 1.00 x | left-guided traversal |
| 50% | binary | restriction | 1,536 | 2,017 | 0.023 | 0.020 | 1.16 x | top-level prefix filter |
| 50% | binary | raffination | 22,464 | 29,485 | 0.044 | 0.046 | 0.95 x | complement of the prefix filter |
| 50% | binary | composition | 576,000,000 | 756,031,501 | 4.939 | 4.899 | 1.01 x | no selective consumer; full product is materialized |
| 50% | n-ary | three-way intersection | 12,000 | 15,751 | 0.165 | 0.048 | 3.42 x | evalZ flattens nested intersections and starts from the sparse overlap operand |
| 50% | unary | wrap | 24,000 | 31,502 | 0.003 | 0.004 | 0.68 x | virtual prefix node |
| 50% | unary | unwrap | 24,000 | 31,501 | 0.003 | 0.027 | 0.12 x | descend through virtual prefix |
| 50% | unary | tails-union | 18,004 | 22,506 | 0.672 | 0.676 | 0.99 x | join every first-level tail |
| 50% | unary | tails-intersection | 4 | 6 | 0.872 | 0.798 | 1.09 x | meet every first-level tail |
| 50% | unary | prefix-closure | 31,500 | 31,501 | 1.126 | 1.149 | 0.98 x | all non-empty prefixes |
| 50% | unary | suffix-closure | 48,008 | 60,010 | 5.002 | 4.885 | 1.02 x | all non-empty suffixes |
| 50% | unary | tails-closure | 48,009 | 60,010 | 5.381 | 5.875 | 0.92 x | epsilon plus suffix closure |
| 50% | range | first(512) | 512 | 673 | 0.009 | 0.014 | 0.63 x | ordered border slice |
| 50% | range | last(512) | 512 | 673 | 0.143 | 0.130 | 1.10 x | ordered border slice |
| 50% | combination | union then exact intersection | 1 | 4 | 0.163 | 0.178 | 0.92 x | selective consumer over a virtual union |
| 50% | combination | diff then restriction | 552 | 737 | 0.127 | 0.071 | 1.78 x | left-guided diff under prefix filter |
| 50% | combination | product exact intersection | 1 | 7 | 4.940 | 2.267 | 2.18 x | selector should avoid the full product |
| 50% | combination | product prefix restriction | 24,000 | 31,504 | 4.893 | 2.151 | 2.27 x | one product row selected by prefix |
| 50% | combination | tails of restricted union | 1,708 | 2,136 | 0.242 | 0.105 | 2.29 x | join tails after a logical prefix filter |
| 50% | combination | range of union | 512 | 673 | 0.227 | 0.238 | 0.95 x | border slice over a virtual union |
| 90% | binary | union | 25,800 | 33,751 | 0.052 | 0.053 | 0.99 x | merge two aligned huge tries |
| 90% | binary | intersection | 22,200 | 29,251 | 0.052 | 0.074 | 0.70 x | walk only common child keys |
| 90% | binary | subtraction | 1,800 | 2,401 | 0.028 | 0.030 | 0.93 x | left-guided traversal |
| 90% | binary | restriction | 1,536 | 2,017 | 0.018 | 0.024 | 0.77 x | top-level prefix filter |
| 90% | binary | raffination | 22,464 | 29,485 | 0.091 | 0.093 | 0.98 x | complement of the prefix filter |
| 90% | binary | composition | 576,000,000 | 756,031,501 | 10.099 | 8.588 | 1.18 x | no selective consumer; full product is materialized |
| 90% | n-ary | three-way intersection | 21,600 | 28,351 | 0.083 | 0.056 | 1.48 x | evalZ flattens nested intersections and starts from the sparse overlap operand |
| 90% | unary | wrap | 24,000 | 31,502 | 0.003 | 0.003 | 1.05 x | virtual prefix node |
| 90% | unary | unwrap | 24,000 | 31,501 | 0.002 | 0.003 | 0.89 x | descend through virtual prefix |
| 90% | unary | tails-union | 18,004 | 22,506 | 0.614 | 0.652 | 0.94 x | join every first-level tail |
| 90% | unary | tails-intersection | 4 | 6 | 0.675 | 0.663 | 1.02 x | meet every first-level tail |
| 90% | unary | prefix-closure | 31,500 | 31,501 | 1.101 | 1.094 | 1.01 x | all non-empty prefixes |
| 90% | unary | suffix-closure | 48,008 | 60,010 | 6.146 | 5.512 | 1.12 x | all non-empty suffixes |
| 90% | unary | tails-closure | 48,009 | 60,010 | 5.355 | 5.231 | 1.02 x | epsilon plus suffix closure |
| 90% | range | first(512) | 512 | 673 | 0.003 | 0.004 | 0.92 x | ordered border slice |
| 90% | range | last(512) | 512 | 673 | 0.018 | 0.017 | 1.03 x | ordered border slice |
| 90% | combination | union then exact intersection | 1 | 4 | 0.052 | 0.069 | 0.75 x | selective consumer over a virtual union |
| 90% | combination | diff then restriction | 72 | 97 | 0.028 | 0.023 | 1.24 x | left-guided diff under prefix filter |
| 90% | combination | product exact intersection | 1 | 7 | 4.941 | 2.244 | 2.20 x | selector should avoid the full product |
| 90% | combination | product prefix restriction | 24,000 | 31,504 | 5.004 | 2.125 | 2.36 x | one product row selected by prefix |
| 90% | combination | tails of restricted union | 1,228 | 1,536 | 0.095 | 0.055 | 1.72 x | join tails after a logical prefix filter |
| 90% | combination | range of union | 512 | 673 | 0.106 | 0.125 | 0.84 x | border slice over a virtual union |

Ratios above `1.00 x` mean the zipper evaluator is faster. Direct `composition` intentionally has no selective consumer, so it is a useful overhead baseline rather than the expected zipper win. Selective product rows exercise composition without forcing the full product before the final materialization boundary.
