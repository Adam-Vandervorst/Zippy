# Review 5 response

Review 5 correctly moved the cost work from fitted time to representation-level
asymptotics. The primary analysis target is now a normalized or supercompiled
residual with annotated arguments, not the source definition and not concrete
evaluation output.

| Concern | Resolution | Permanent gate |
| --- | --- | --- |
| Restriction wrongly grows with the source | Trie restriction visits only the right prefix trie and grafts accepted source subtries. Raffination is modeled as two prefix-driven traversals. Unwrap charges only prefix descent. | Asymmetric source-growth counter cases plus a dedicated 4,096-path unwrap case. |
| Disjoint fast path lost on large literals | Exact literals retain a bounded head-trie projection even when per-path strata exceed the pattern cap. Complete, disjoint tracked heads select the constant root rejection. | Intersection/subtraction at 64, 512, and 4,096 paths perform one executor node visit. |
| Composition was modeled as a Cartesian materialization | Trie concat traverses the left trie and grafts the right by reference, so its cost is independent of right size. | Separate left-growth and right-growth counter families on normalized programs. |
| Scalar units and fitted residuals are incomparable | `SpatialCostComponents` carries `nodeVisits`, `patriciaVisits`, `pathComparisons`, `allocations`, and `rounds`; all executors tick matching scoped counters. Fitted ns/unit and residual gates were removed. | Every component prediction is at least its counter. The ≤8× tightness gate applies to the four topology-independent components; Patricia retains soundness and stable/growth gates, while its ≤8× ratios describe the canonical focused interning order. The exact cross-executor three-round iteration remains, and wall Spearman is smoke-only. |
| `TrieSpace.node` makes persistent insertion quadratic in width | `insertItems` derives aggregate deltas and calls constant-time `nodeKnown`; duplicate insertion returns the existing trie. Bulk constructors retain the scanning constructor. | Exact scan/allocation assertions for wide/deep construction, `joinAll`, and zipper focus insertion. |
| Symmetric cost corpus hides operand dependence | The corpus fixes one operand and grows the other independently for restriction, raffination, intersection, subtraction, composition, and unwrap. | Explicit constant-class and traversed-operand-growth assertions for trie, zipper, and graph. |
| Costing definitions misrepresents deployed work | `Supercompiler.optimizedSpatialType(routine, annotations, routines)` normalizes the body while retaining abstract arguments, then runs abstract interpretation. | Both counter and wall-clock corpora use this entry point and execute the same normalized open program. |

The construction benchmark's 16,384-wide row fell from the review's 921.833 ms
to 0.799 ms on the final focused run (about 1,154×); the exact counter gate, rather
than that noisy wall time, is the lasting complexity guarantee. The corresponding
deep row was 3.219 ms versus 15.474 ms in the review baseline.
