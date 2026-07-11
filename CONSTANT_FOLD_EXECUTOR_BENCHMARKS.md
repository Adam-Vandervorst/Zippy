# Constant Fold Executor Report

Focused sweep over the four previously reported long constant-fold rows. `speedup vs reference` compares total constant-fold executor time within the same focused run.

| benchmark | backend | compile ms | source pass ms | const-fold total ms | speedup vs reference | eval ms | evalTrie ms | evalZ ms | execT ms | eval calls | evalTrie calls | evalZ calls | execT calls | total calls |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| life compile-pass random 24x24 initial literal | Reference | 31.713 | 30.749 | 26.845 | 1.00 x | 26.845 | 0.000 | 0.000 | 0.000 | 52 | 0 | 0 | 0 | 52 |
| sliding puzzle 3x3 pure compile-pass depth-8 step | Reference | 43.294 | 43.025 | 40.353 | 1.00 x | 40.353 | 0.000 | 0.000 | 0.000 | 224 | 0 | 0 | 0 | 224 |
| n-queens MORKL 8x8 source graph compile | Reference | 557.596 | 556.427 | 548.184 | 1.00 x | 548.184 | 0.000 | 0.000 | 0.000 | 178 | 0 | 0 | 0 | 178 |
| n-queens MORKL 8x8 compile-pass | Reference | 549.928 | 549.684 | 542.508 | 1.00 x | 542.508 | 0.000 | 0.000 | 0.000 | 178 | 0 | 0 | 0 | 178 |
| life compile-pass random 24x24 initial literal | Trie | 1069.834 | 1069.216 | 1065.410 | 0.03 x | 0.000 | 1065.410 | 0.000 | 0.000 | 0 | 52 | 0 | 0 | 52 |
| sliding puzzle 3x3 pure compile-pass depth-8 step | Trie | 412.580 | 412.365 | 410.394 | 0.10 x | 0.000 | 410.394 | 0.000 | 0.000 | 0 | 224 | 0 | 0 | 224 |
| n-queens MORKL 8x8 source graph compile | Trie | 1341.603 | 1340.903 | 1334.638 | 0.41 x | 0.000 | 1334.638 | 0.000 | 0.000 | 0 | 178 | 0 | 0 | 178 |
| n-queens MORKL 8x8 compile-pass | Trie | 1473.917 | 1473.707 | 1467.416 | 0.37 x | 0.000 | 1467.416 | 0.000 | 0.000 | 0 | 178 | 0 | 0 | 178 |
| life compile-pass random 24x24 initial literal | Zipper | 1110.061 | 1109.557 | 1105.394 | 0.02 x | 0.000 | 0.000 | 1105.394 | 0.000 | 0 | 0 | 52 | 0 | 52 |
| sliding puzzle 3x3 pure compile-pass depth-8 step | Zipper | 417.955 | 417.745 | 415.882 | 0.10 x | 0.000 | 0.000 | 415.882 | 0.000 | 0 | 0 | 224 | 0 | 224 |
| n-queens MORKL 8x8 source graph compile | Zipper | 1597.222 | 1596.292 | 1589.783 | 0.34 x | 0.000 | 0.000 | 1589.783 | 0.000 | 0 | 0 | 178 | 0 | 178 |
| n-queens MORKL 8x8 compile-pass | Zipper | 1553.318 | 1553.113 | 1547.457 | 0.35 x | 0.000 | 0.000 | 1547.457 | 0.000 | 0 | 0 | 178 | 0 | 178 |
| life compile-pass random 24x24 initial literal | ExecT | 21.494 | 21.062 | 17.249 | 1.56 x | 0.000 | 0.000 | 0.000 | 17.249 | 0 | 0 | 0 | 52 | 52 |
| sliding puzzle 3x3 pure compile-pass depth-8 step | ExecT | 81.878 | 81.621 | 79.783 | 0.51 x | 0.000 | 0.000 | 0.000 | 79.783 | 0 | 0 | 0 | 224 | 224 |
| n-queens MORKL 8x8 source graph compile | ExecT | 397.957 | 396.134 | 389.203 | 1.41 x | 0.000 | 0.000 | 0.000 | 389.203 | 0 | 0 | 0 | 178 | 178 |
| n-queens MORKL 8x8 compile-pass | ExecT | 348.133 | 347.891 | 341.176 | 1.59 x | 0.000 | 0.000 | 0.000 | 341.176 | 0 | 0 | 0 | 178 | 178 |
| life compile-pass random 24x24 initial literal | Hybrid | 17.491 | 17.017 | 12.708 | 2.11 x | 1.915 | 0.000 | 0.000 | 10.793 | 50 | 0 | 0 | 2 | 52 |
| sliding puzzle 3x3 pure compile-pass depth-8 step | Hybrid | 42.459 | 42.225 | 40.275 | 1.00 x | 40.275 | 0.000 | 0.000 | 0.000 | 224 | 0 | 0 | 0 | 224 |
| n-queens MORKL 8x8 source graph compile | Hybrid | 489.232 | 488.552 | 481.673 | 1.14 x | 481.673 | 0.000 | 0.000 | 0.000 | 178 | 0 | 0 | 0 | 178 |
| n-queens MORKL 8x8 compile-pass | Hybrid | 442.029 | 441.826 | 435.693 | 1.25 x | 435.693 | 0.000 | 0.000 | 0.000 | 178 | 0 | 0 | 0 | 178 |
