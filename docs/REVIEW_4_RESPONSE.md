# Review 4 response

This is the historical Review 4 response. Review 5 subsequently demonstrated
that the scalar calibration below did not certify asymptotics; it has been
removed and replaced by typed executor counters and asymmetric normalized-program
gates documented in `REVIEW_5_RESPONSE.md`.

| Concern | Resolution | Permanent gate |
| --- | --- | --- |
| Rank-only cost validation misses magnitude | Superseded: unlike scalar operations cannot share a unit. Cost now tracks node visits, path comparisons, allocations, and rounds. | `SpatialCostCounterTest` compares each component to executor counters; `SpatialCostCorrelationTest` is wall-clock smoke only. |
| `SpatialType.scala` remains monolithic | `SpatialType.scala` now contains the domain, symbolic bounds, CSP values, and decorated results; the interpreter and transfer implementation moved to `SpatialAnalyzer.scala`. | Normal whole-project compilation and the complete spatial suite. |
| Guarded specializer has no production caller | `SpatialCompilation` now lives beside `SpatialSpecializer`; `Supercompiler.specialize` derives annotations from syntactically concrete arguments, calls `selectApplicable`, and installs the residual only when `applicableTo` accepts those arguments. The report retains the exact spatial rewrite facts used. | A production-pipeline test checks selection, recorded facts, and evaluation equivalence; the guarded residual corpus checks broader equivalence. |

The former fitted-scale results are retained only as historical Review 4 data;
they are not a current design claim or gate. The balanced analyzer scaling run
remained linear through 32,768 leaves (57.527, 67.621, 157.302, 317.915, 573.570,
and 1,132.108 ms from 1,024 through 32,768 leaves); absolute times reflect the loaded
machine, while the final five doublings preserve the expected linear trend.
