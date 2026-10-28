# Result path-length audit

The paired baseline/Z3 audit uses the canonical reproducible corpus:

```scala
SpaceFuzzerCorpus.generate(1000, 20260708L, 5, 400)
```

Every program is evaluated once, then its concrete minimum and maximum path lengths are checked against both analyses under the same input context. The runner fails immediately if a bound is violated or if the Z3 result weakens its compositional fallback.

## Canonical 1,000-program result

- Sound lower bounds: 1,000 / 1,000
- Sound upper bounds: 1,000 / 1,000
- Finite upper bounds: 1,000 / 1,000
- Exact lower bounds: 851 / 1,000
- Exact upper bounds: 831 / 1,000
- Z3 lower improvements over baseline: 49
- Z3 upper improvements over baseline: 36
- Mean lower underestimate: 0.233 path items
- Mean upper overestimate: 0.303 path items
- Least-tight lower: program 596, gap 5
- Least-tight upper: program 815, gap 7

| Additive gap | Lower programs | Upper programs |
|---:|---:|---:|
| 0 | 851 | 831 |
| 1 | 86 | 88 |
| 2 | 46 | 49 |
| 3–4 | 16 | 26 |
| 5–8 | 1 | 6 |
| >8 | 0 | 0 |

The requested impossible-intersection example has compositional bounds `[2, 21]`. Z3 proves that its length-15 intersection region is empty, leaving epsilon on the left of the product and refining the result to the concrete `[2, 6]`.

## Scaling guard

The Boolean encoder stops as soon as a component exceeds the configured eight-atom budget. On balanced unions of distinct singleton leaves, seven-sample median refined graph-construction times were:

| Leaves | Refined construction | Warm bound evaluation |
|---:|---:|---:|
| 1,024 | 13.626 ms | 0.965 ms |
| 2,048 | 10.801 ms | 0.533 ms |
| 4,096 | 13.983 ms | 0.453 ms |
| 8,192 | 27.708 ms | 0.282 ms |
| 16,384 | 57.053 ms | 0.311 ms |
| 32,768 | 114.014 ms | 0.453 ms |

The large-input trend is linear. Z3 queries are memoized by Boolean topology, cardinality bounds, and structural relations; path-length endpoints are applied to the feasible-region result without requiring another solver process.
