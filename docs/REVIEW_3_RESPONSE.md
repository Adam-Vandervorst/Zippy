# Review 3 response

This file maps the actionable concerns in `review.md` to the production API,
tests, proof artifacts, and measured gates added in response. `whispers.md` was
used as design input, but its suggested formulas were retained only where they
matched the actual executors and the represented gamma semantics.

| Concern | Resolution | Permanent gate |
| --- | --- | --- |
| No usable Q1 API | `SpatialMembership.satisfies` exposes the populated-envelope check; `gammaMember` exposes full concretization membership with overlapping-class cover semantics. | Generated positive/negative membership corpus and all random audits. |
| Pattern equality rejects signatures | `SpatialItem`/`SpatialPattern.isSubsumedBy` implements constant, affine-domain, and unknown inclusion; affine membership preserves repeated-variable equality. | `SpatialTypeTest` signature cases. |
| Unguarded specializations | `SpecializedRoutine` carries path/space preconditions and checks them with full gamma membership. | Annotation-only firing test and 1,000-program residual corpus. |
| Iteration/fixpoint cost omitted | Cost has work, allocation, and rounds. Iteration charges group/body/collect; fixpoint retains a checked symbolic round bound. | Focused fat-fiber/four-head tests and full corpus. |
| One generic backend formula | `SpatialCostModel` has reference, trie, zipper, and graph implementations with operation-specific transfers. Review 5 supersedes the old scalar calibration with typed executor counters. | Per-backend typed counter bounds on asymmetric normalized programs; Spearman is smoke-only. |
| Recursive cost becomes free/infinite | Recursive edges emit named markers. Tails, positive unwrap, and iterator-rest decreases close linear recurrences against annotated maximum depth; unsupported recurrences remain named. | Tails-recursive routine test and asymptotic-order test. |
| Missing prefix/head channel | `SpatialHeadShape` is a bounded abstract trie with epsilon presence, tracked children, untracked head count, and untracked-tail summary. | Fat-fiber versus four-head test; degree/facts tests. |
| Monolithic implementation | The domain/CSP and analyzer/transfer core are now separate, in addition to membership, shape, facts, costs, recursion, specialization, and law registry modules. | Normal compilation boundary. |
| `TermLimit` creates infinity | Cost sums use shallow chunks or finite named atoms; rendering alone is budgeted. | Finite-cost and large balanced-union scaling tests. |
| Analysis has no production consumer | `SpatialCompilation` owns guarded specialization and `Supercompiler.specialize` invokes it as a production stage, selecting only residuals whose precondition accepts the concrete arguments. | Production-stage selection test, corpus equivalence, and annotation-only tests. |
| Only positive proof claims | `SpatialLawRegistry` records `Proved` and `Refuted`; subtraction right-union distribution and restriction commutativity have concrete witnesses and expected-`sat` SMT controls. | Full generated Z3/egg proof pipeline. |
| Exact inputs hide unsoundness | Open and adversarial audits pass declared abstract inputs into analysis; concrete values are downstream witnesses only. | Historical, extended, and approximate-input 1,000-program runs. |

## Final measured gates

- Exact historical corpus: 1,000/1,000 sound; optimized 1,000/1,000; 698 exact
  sizes; 885 exact global length bounds; no unbounded audited projections.
- Historical open corpus: 1,000/1,000 sound, all size uppers finite. Extended
  open corpus: 1,000/1,000, all 24 constructors, 279 cross-routine calls.
- Approximate-input adversarial gamma: 1,000/1,000. Guarded residual corpus:
  1,000/1,000 preserved.
- Cost Spearman: reference 1.000, trie 0.800, zipper 1.000, graph 1.000.
- Balanced spatial analysis remains linear through 32,768 leaves; final median
  is 826.644 ms versus the review baseline 611.989 ms (1.35x constant factor).
- The independent-product rewrite runs 5.76x, 14.43x, 6.91x, and 41.98x faster
  at 32, 64, 128, and 256 heads respectively.
- The full bounded proof pipeline passes, including both negative controls.

Microbenchmarks are noisy and the generated benchmark reports preserve every
row rather than selecting favorable ones. The optional four-row long
constant-fold sweep is excluded from the release gate; an attempted 1.5 GiB
run exhausted heap in its zipper row. The normal mixed trie report, zipper
algebra report, range-tail microbenchmark, independent-product benchmark, and
trie asymptotic benchmark all completed after checking result equality.
