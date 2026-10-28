# Large Zipper Benchmarks

These rows are intentionally larger and more asymptotic than the mixed publication table. They compare direct `evalTrie` against direct `evalZ` after checking both produce the same `TrieSpace` result. Times are medians after two warmup evaluations. The nonrecursive two-hop rows expose generic-iteration scaling; the product rows stress selective traversal, where the source expression denotes an `n x n` product but the consumer asks for one prefix or one exact path.

| benchmark | size | result paths | evalTrie ms | evalZ ms | evalTrie / evalZ | note |
|---|---:|---:|---:|---:|---:|---|
| nonrecursive graph two-hop | 180 nodes, 359 edge facts | 534 | 2.674 | 3.599 | 0.74 x | generic iteration materializes branch tries natively at the final boundary |
| nonrecursive graph two-hop | 360 nodes, 719 edge facts | 1,074 | 2.278 | 4.082 | 0.56 x | generic iteration materializes branch tries natively at the final boundary |
| nonrecursive graph two-hop | 720 nodes, 1439 edge facts | 2,154 | 5.635 | 5.295 | 1.06 x | generic iteration materializes branch tries natively at the final boundary |
| product intersected by one exact path | 2000 x 2000 product, 1 result path | 1 | 0.495 | 0.090 | 5.47 x | large intermediate product should not be materialized by zipper traversal |
| product intersected by one exact path | 10000 x 10000 product, 1 result path | 1 | 6.012 | 0.124 | 48.57 x | large intermediate product should not be materialized by zipper traversal |
| product intersected by one exact path | 30000 x 30000 product, 1 result path | 1 | 7.344 | 0.183 | 40.13 x | large intermediate product should not be materialized by zipper traversal |
| product restricted by one first-level prefix | 2000 x 2000 product, 2000 result paths | 2,000 | 0.393 | 0.022 | 17.75 x | large intermediate product should not be materialized by zipper traversal |
| product restricted by one first-level prefix | 10000 x 10000 product, 10000 result paths | 10,000 | 1.909 | 0.015 | 126.09 x | large intermediate product should not be materialized by zipper traversal |
| product restricted by one first-level prefix | 30000 x 30000 product, 30000 result paths | 30,000 | 9.976 | 0.016 | 643.21 x | large intermediate product should not be materialized by zipper traversal |
| aunt query over large generated family, one queried person | 9 generations x 80 people (2720 facts) | 0 | 0.149 | 0.152 | 0.98 x | large query-shaped dataset with small queried person set |
| aunt query over large generated family, one queried person | 11 generations x 160 people (6720 facts) | 0 | 0.047 | 0.105 | 0.45 x | large query-shaped dataset with small queried person set |
| SCC divide-and-conquer | 6 directed edges, 2 representative/member pairs | 2 | 1.650 | 7.009 | 0.24 x | paper pivot/partition recursion with masked reachability lowered to a native fixpoint |
| semi-naive datalog over generated chain graph | 40 nodes, 79 edge facts | 820 | 45.046 | 25.156 | 1.79 x | recursive union-saturating routine lowered to lazy native-trie synchronous rounds |
| semi-naive datalog over generated chain graph | 80 nodes, 159 edge facts | 3,240 | 150.339 | 108.057 | 1.39 x | recursive union-saturating routine lowered to lazy native-trie synchronous rounds |

A ratio above `1.00 x` means the zipper evaluator is faster. Recursive Datalog is included as a large generated control case and is timed through direct `evalZ` lowering; its state-negative delta subtraction selects lazy exact synchronous rounds executed directly in native trie algebra, while structurally positive, productive recursive steps use prefix-demand cells. An unsupported cell is reserved for a genuine lowering failure.
