# Spatial abstract interpretation

The semantic lattice, complete list of tracked properties, proved transfer laws, and known non-laws are documented in [SPATIAL_TYPE_LAWS.md](SPATIAL_TYPE_LAWS.md).

`SpatialTypeAnalysis` interprets a MORKL program from abstract path/space inputs to an abstract output space. It replaces the old output-side `otypes` experiment, which only collected syntactic variables and could not express cardinality, path length, control flow, or arithmetic relations. The input-side `itypes` experiment remains separate for now.

## Domain

A `SpatialType` is a finite union of `SpatialStratum` values. Each stratum carries:

- a lower/upper path-length interval;
- a lower/upper cardinality interval;
- optionally, a symbolic path pattern.

Patterns contain constants, unknown items, or affine integer items such as `coord.x-1`. Provably different lengths and patterns are disjoint, so their cardinality lower bounds add; possibly overlapping regions use the conservative maximum lower bound. A bounded head-indexed trie projection additionally records epsilon presence, tracked constant heads and their tail summaries, plus bounds and a tail summary for untracked heads. The complete type also exposes total-size and global path-length projections, an explicit inconsistent value (`bottom`), and lower/upper work, allocation, and round bounds for the reference, trie, zipper, and graph backends.

The implementation is split by responsibility: `SpatialType.scala` contains the core domain, bounds, and CSP values; `SpatialAnalyzer.scala` contains the abstract interpreter and transfer laws; `SpatialShape.scala` contains the bounded trie projection; `SpatialMembership.scala` concretization checks; `SpatialFacts.scala` resolved optimizer facts; `SpatialCostModel.scala` the cost domain and executor models; and `SpatialSpecializer.scala` guarded residualization and its compilation-stage selection API.

## Membership and guarded residuals

`SpatialMembership.satisfies(value, declared)` is the signature-envelope API. It checks totals, lengths, coverage, and every populated class; lower bounds on an unpopulated class are intentionally ignored. `SpatialMembership.gammaMember(value, declared)` is exact membership in the represented concretization. Overlapping classes are simultaneous predicates and may count the same path; truly identical classes are canonicalized first, combining lower bounds by `max` and upper bounds additively (with exact singleton classes capped at one).

More precisely, stratum uppers define an existential cover: every concrete path
must be attributable to a matching class without exceeding that class's upper
capacity. Lower obligations are predicates and may share a concrete witness
across overlapping classes. This avoids both unsound readings of overlap: a
broad class does not own every matching path contributed by another union arm,
and one path need not be duplicated merely to witness two compatible lower
facts.

Pattern inclusion is item-wise: a constant is included by the same constant, a compatible affine domain, or an unknown item; an affine item is included by a sufficiently wide affine item or unknown. Repeated affine variables must bind consistently during concrete membership. Thus a concrete `k.a` type is below a declared `k.?v` type.

`SpatialCompilation.specialize` consumes only `SpatialRoutineAnnotations` and returns `SpecializedRoutine(precondition, residual, facts)`. It eliminates abstractly dead nodes, folds proved constants, and applies empty identities. `applicableTo` checks real space arguments with full gamma membership (and path arguments against their path types), so a conditionally valid residual cannot be installed unconditionally. `Supercompiler.specialize` is the production consumer: it derives exact annotations only for syntactically concrete call arguments, calls `SpatialCompilation.selectApplicable`, and installs the residual only after that guard succeeds. The selected facts are retained in `SupercompileReport.spatialRewriteFacts`.

`SpatialAssumptions` maps free space mentions and path references to input types.
`SpatialPrefixCoverage(k, xs, lengths, minimumMatches)` is an optional,
quantitative dependency asserting that `k` selects at least `minimumMatches`
paths from `xs` at the selected lengths (the default is one). Restriction keeps
one aggregate witness per exact length: witnesses for overlapping patterns or
prefixes combine by maximum, while distinct path lengths may add. It attaches
the witness to a stratum only when that stratum is the sole class at its length,
so one global match is never duplicated across disjoint patterns. This
dependency is necessary for positive restriction lower bounds: knowing only
that `k` has length three cannot prove that an arbitrary length-four path starts
with `k`.

Iteration is group-sensitive. A constant head has at most one group when its
source is nonempty; an affine head has at most the size of its declared domain;
and an unknown head falls back to source cardinality. The bound tail denotes an
entire fiber, not one arbitrary path, so a constant-headed stratum passes its
full cardinality into the body. Canonical nested iterator chains that consume a
complete source path are additionally interpreted pointwise: their total upper
is the number of source paths times the per-path leaf result, instead of a
product of independent group estimates. The scalar size analysis recognizes
the same pointwise map forms through nested iteration, fixed-path products,
wrap/unwrap, selectors, and unions. An injective head/tail reconstruction arm
also preserves the headed source lower bound even when a correlated sibling
arm has a weak lower estimate.

`outputRoutine` and its compatibility alias `outputRoutineAbstract` (also
exposed as `Supercompiler.abstractSpatialType`) always interpret a routine body
from argument annotations. Neither invokes the concrete evaluator, even when
all inputs are exact constants or the routine has no arguments. A closed syntax
tree therefore cannot silently turn an abstract-interpretation experiment into
execution.

The strict API takes one `SpatialRoutineAnnotations` value containing path and
space argument types, prefix coverage, and `SpatialBoundLaw` result-type laws.
Those laws are input annotations, not evaluator callbacks or facts learned from
an output. They intersect the structural cardinality with facts such as
subset-of-image multiplicity, source containment, directed-closure bounds,
divide-and-conquer SCC representative bounds, a finite universe, or a connected finite component.
Production laws derive sliding-puzzle component capacity from board width and
n-queens constraints from board size. The generic exact-count law accepts an
annotated `FiniteIntConstraintProblem`; there is deliberately no raw
`ExactCardinality(number)` hook. Structural and semantic evidence form a
reduced product: neither side can weaken the other. An exact semantic claim
that contradicts an exact structural result produces `bottom`; it is never
substituted for the structural result.

`FiniteIntConstraintProblem` is the first small relational component. It counts
finite-domain assignments subject to all-different, disequality, and absolute-
difference constraints. `FiniteIntConstraintProblem.nQueens(n)` constructs the
production constraint problem, and `NQueensSolutions(n)` uses it without
executing the MORKL generator. `SlidingPuzzleReachability(seed,width)` similarly
uses the production factorial/parity capacity, while `RepresentativeScc(edges)`
gives the sound `[0,2E]` representative/member envelope. Counting has a deterministic node budget;
budget exhaustion contributes no refinement. See
[CORNERSTONE_ABSTRACT_INTERPRETATIONS.md](CORNERSTONE_ABSTRACT_INTERPRETATIONS.md)
for the contracts and all seven cornerstone results. The checked
[generated summary](CORNERSTONE_ABSTRACT_INTERPRETATIONS_GENERATED.md) records
the deterministic output of the production analysis entry point.

## Example

For input strata

```text
xs = length 2: 5 paths; length 4: 7 paths; length 6: 9 paths
ys = empty
len(k) = 3
k prefixes xs at lengths 4 and 6
```

the type of

```text
TailsUnion(xs <| (ys ∪ {k}))
```

is:

```text
length 3: [1, 7] paths
length 5: [1, 9] paths
total:    [2, 16] paths
```

Without the prefix-coverage fact, the sound lower cardinalities are zero, while the upper type is unchanged.

## Encoded control flow

The iterator encoding used by `on_empty` is recognized structurally. For

```text
s ∪ s.on_empty(g)
```

the exact total size is represented by the arithmetic expression

```text
ifZero(|s|, |g|, |s|)
```

and each length stratum is guarded by the same condition. This preserves the two elaborated cases directly rather than losing their exclusivity in independent interval additions.

## Pure arithmetic and Game of Life

Unwrapping a two-column integer literal relation recognizes a uniform affine map when the abstract input range is inside the relation domain. Consequently `decr(x)`, `ident(x)`, and `succ(x)` become the distinct patterns `x-1`, `x`, and `x+1`.

For an abstract two-coordinate input, the pure `LifeExample.neigh` routine therefore derives:

- three alternatives for each coordinate;
- nine distinct Cartesian-product patterns;
- removal of the exact center pattern;
- exactly eight output paths, all of length two.

Exact constant spatial inputs form the constant subdomain. A five-step glider
is analyzed as one nested open expression: each abstract output feeds the next
abstract call, while no concrete intermediate result does. The resulting bound
retains exact path length three and contains the final five-cell result. A
separate evaluator call runs only after analysis to check soundness.

## Optimization facts and graph fibers

`SpatialType.facts` is the stable optimizer-facing API. It resolves
`definitelyNonEmpty`, `definitelyAtLeast(n)`, `definiteSize`, `maxDepth`,
`depthProfile`, `definitePathAt(n)`, `commonConstantPrefix`, and `isDead`
without exposing `SizeExpr` resolution rules to each consumer.

`fiberDegree(prefixLength)` reports minimum degree, maximum degree, edge count,
key count, and the average as an edge/key ratio. It is exact for constant types.
For symbolic patterns, constants contribute one choice, affine items contribute
their finite domain capped by stratum cardinality, and unknown items contribute
the stratum cardinality. Symbolic key lower bounds use suffix capacity
(`ceil(edges/suffixCapacity)`), while minimum/maximum fiber bounds use the
derived key interval and maximum suffix capacity. `depthProfile` lifts the same
rule to every item depth. Iterator bodies of the exact form `relation(head)`
consume these bounds directly: selected-key count times maximum degree caps the
upper, and quantitative prefix coverage supplies a lower witness without
assuming different keys have disjoint suffixes. Arbitrary key-specific degree
correlation is still outside the domain. For
`{edge.a.b, edge.a.c, edge.b.c}` at prefix length two it reports minimum degree
1, maximum degree 2, three edges, two keys, and average `3/2`.

`SpatialBackendSelection.candidates` converts those facts into optimization
recommendations: bounded-depth trie unrolling, common-prefix zipper pre-focus,
and exact-value graph constant folding. An executable rewrite is instead
returned by `SpatialCompilation.specialize`, whose precondition travels
with the residual.

## Cardinality-preserving caps

Every selector-like transfer retains the total source cap even when its strata
must be summarized: intersection is capped by both operands; subtraction,
restriction, range, tails-union, and unwrap by their selected source; and
composition by the product of operand totals. These scalar caps are part of the
same reduced product as the shape strata and prevent a lossy shape split from
inventing a larger total.

The `SizeExpr` normalizer uses only universally valid natural-number order
facts. It flattens extrema and products, makes Boolean indicators idempotent,
uses `positive(x) <= x`, and removes a dominated branch of a minimum/maximum
when a structural proof succeeds. It deliberately leaves incomparable
polynomials intact. Dominance checks are identity-memoized and rendering has a
64-node budget, so diagnostics cannot recursively print megabytes of repeated
terms. `SizeExpr.growth` is a separate dominant-monomial antichain over a
declared parameter set; it can, for example, prove `E` grows no faster than
`E²` without confusing asymptotic order with pointwise natural-number order.

`fromStrata` canonicalizes duplicate classes and exact singleton capacities.
An already-canonical vector takes an allocation-free fast path; full grouping
and sorting occurs only when a duplicate or singleton cap actually requires it.
Reduced-product closure is performed at semantic transfer points that introduce
cross-component facts and at every public analysis boundary.

## Fixpoints, intermediate results, and cost

`Fixpoint` is interpreted by ascending iteration. Before returning a widened
shape invariant, the analyzer applies the step again and requires a
post-fixpoint in the implementation order. Cardinalities may widen to infinity;
if that check or the resource limit fails, every spatial component becomes top.
One-unrolling shapes are never exposed as a fixpoint invariant.

`outputDecorated` returns the root and every syntactic occurrence, identified by
its child-index path from the root, together with the lexical path/space
bindings under which it was analyzed. `atPosition` selects one occurrence even
when two subterms are structurally equal. Repeated observations of that
occurrence under loop/fixpoint bindings are retained, and `result` is their
lattice `joinAlternatives` summary.

The cost component propagates symbolic lower/upper work, allocation, and round
bounds. Its certified upper surface is split into named representation events:
`nodeVisits`, `patriciaVisits`, `pathComparisons`, `allocations`, and `rounds`. `SpatialCostModel`
has one implementation per executor, and the executors expose matching scoped
counters. Transfers are derived from the relevant representation. Iteration
charges grouping plus each body cost scaled by its head groups plus collection;
fixpoint work is scaled by a sound symbolic round bound. Recursive costs use
`SpatialRecurrence.solve`, fed by a syntax-only decreasing-measure detector for
tails, non-empty unwraps, and iterator rests. Its closed form is the executable
natural-number expression `additive * geomSeries(branching, rounds)`; constant
arguments evaluate exactly (for example `3 * geomSeries(2,4) = 45`) and the
asymptotic projection distinguishes linear from exponential recurrence growth.
A recurrence is closed only when every self-call decreases; otherwise named
recursive work/allocation/round atoms remain visible.

Patricia work is not treated as a constant multiple of semantic trie visits.
Composition is bounded by the Patricia nodes of the traversed left trie;
head-disjoint boolean algebra takes one Patricia visit; general boolean algebra
is bounded by both operand representations. Restriction combines twice the
prefix-trie nodes with the source child-map frontiers reached by those prefix
depths. The asymmetric permanent gate checks this fifth component independently,
including constant behaviour when an irrelevant operand grows and monotone
growth when the traversed operand grows.

The production-facing entry point is `Supercompiler.optimizedSpatialType`.
For routines it normalizes the body while preserving abstract path and space
arguments, then interprets that residual. Thus the model predicts the program
that the optimized executor runs without evaluating or inlining its inputs.
`SizeExpr.asymptotic` projects polynomial, log, and geometric atoms to a dominant
order.

Cost addition no longer has a `TermLimit => Infinity` precision cliff. Small
finite sums are stored as shallow chunks and large ones as named finite-sum
atoms, while the rendering budget controls only presentation. The permanent cost
gate uses asymmetric operands on normalized open programs: one operand is fixed
while the other grows. For each optimized executor and each typed component,
predictions must bound the matching counter and remain within a small constant
factor. It also asserts the relevant complexity class: restriction and
raffination do not grow with the source; head-disjoint intersection/subtraction
do not descend either operand; composition does not grow with the grafted right
trie; unwrap depends only on prefix length. No nanoseconds-per-unit calibration
or fitted residual is involved. A separate wall-clock Spearman test remains only
as a noisy end-to-end smoke check.

## One-way validation

Validation is deliberately downstream of analysis:

```text
annotated inputs + syntax + annotated semantic laws -> abstract result
concrete inputs + evaluator                           -> validation only
```

No concrete result, fixture cardinality, or evaluator-derived path shape is an
input to either spatial routine entry point or to the cornerstone report.
Numerical audits use `annotatedBound`, which resolves constants, propagated
one-sided arithmetic, and Z3 constraints from their abstract atom bounds.
Opaque `SizeOf`/minimum-length/maximum-length atoms contribute only their safe
zero/infinity envelope; the legacy `evaluate` helper is reserved for downstream
concrete validation. `ResultSpaceSize.estimateReported` and
`SpatialTypeAnalysis.outputReported` return structured `Z3Diagnostic` values for
process timeouts, solver timeouts/unknowns, nonzero exits, and I/O failures while
retaining the compositional fallback. A timeout is also printed when it fires;
failure to start the configured Z3 executable is a hard error rather than silent
degradation.

The opt-in extended corpus generates all 24 `Space` constructors, including
cross-routine `Call`, `Empty`, raffination, fold, bounded fixpoints, every closure/tails form, and grounded space operations in addition
to the original operators. The default generator deliberately preserves the
canonical seed's historical program/input sequence for paired comparisons. A
concrete-input run is a soundness oracle for those witnesses, not evidence of
open-program precision. The open audit instead uses a declared
ranged-length/cardinality input type and checks concrete witnesses only after
analysis.

For `generate(1000, 20260708L, 5, 400)`, the concrete-input audit was
1,000/1,000 sound, with 698 exact sizes, 885 exact global length intervals,
988 exact-length stratum checks, and no unbounded audited projection. The
identical programs and witnesses under the declared open input type were also
1,000/1,000 sound: all upper bounds were finite, 25 sizes were exact, and upper
slack was distributed as 104 exact, 34 within 1–2, 20 within 3–8, 453 within
9–32, and 389 at 33 or more. The extended run covered all 24 constructors and
279 cross-routine calls; 437 upper bounds were finite and all 1,000 witnesses
were sound. A separate 1,000-program approximate-input adversarial run passed
full gamma membership 1,000/1,000, and guarded specialization preserved the
same 1,000 concrete results.

Pattern retention is capped (64 by default). The cap is an explicit
`SpatialAnalysisConfig` field in the assumptions rather than a JVM-global flag.
Overflow is merged into length strata with preserved cardinality bounds;
alternatives are never truncated.

The permanent `spatialTypeScalingAudit` guard measures balanced unions. On this
implementation, seven-sample medians for 1,024/2,048/4,096/8,192/16,384/
32,768 leaves were 42.637/53.318/104.080/211.232/414.589/826.644 ms. The large
end remains linear. Against the preceding review baseline
40.912/43.102/78.010/157.389/309.807/611.989 ms, the final large point is 1.35x
slower from canonical gamma classes and four backend cost intervals; the
allocation-free canonical fast path reduced the transient 1,383.732 ms result
to 826.644 ms.
