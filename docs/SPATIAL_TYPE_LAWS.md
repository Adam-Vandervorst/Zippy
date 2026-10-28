# Spatial abstract-interpretation laws

This document records two related layers. The generated FOL obligations model
the semantic set-interval lattice `[must,may]`. Unbounded bridge obligations
formalize constructor induction, the post-fixpoint induction step,
optimizer/evaluator preservation, and guarded backend selection. A separate
generated bounded theorem maps every three-element set interval into live
production `SpatialType`, records the actual production operations through a
fail-closed decoder, and asks Z3 for a mismatch with independent bit-vector
interval semantics. Neither layer constitutes machine extraction or a
line-by-line proof of the full Scala interpreter.

## Information carried by the implementation

The analysis currently uses all of the following information.

| Component | Information and use |
| --- | --- |
| Symbolic path item | Constant item, unknown item, or an affine integer item `x + k` with a domain for `x`. Used to prove equality, disjointness, and arithmetic relations. |
| Symbolic path pattern | Ordered vector of symbolic items. Used by concatenation, prefix tests, unwrap, restriction, and exact-value recovery. |
| Path-expression type | Alternative patterns plus a lower/upper length interval. A path expression still denotes one path; its patterns are alternatives. |
| Spatial stratum | Pattern or length region together with a lower/upper cardinality. Provably disjoint strata have additive lower bounds; overlapping strata use their maximum lower bound. |
| Bounded head shape | Epsilon presence, tracked constant heads with recursive tail summaries, and cardinality/tail summaries for untracked heads. It refines iteration groups, prefix counts, and per-depth degree without truncating overflow. |
| Total size | Lower/upper result-space cardinality, including symbolic and `ifZero` expressions. |
| Global path length | Minimum/maximum length projected from every nonempty stratum. |
| Exact constant | A finite path set represented path-for-path while below the pattern cap. It is the constant abstract subdomain. |
| Emptiness and positivity | Zero upper means definitely empty; positive lower means definitely nonempty. These facts guard iteration and encoded control flow. |
| Prefix dependency | `SpatialPrefixCoverage` records that a path selects at least `minimumMatches` members of a source fiber at specified lengths. Restriction treats this as an aggregate per-length witness (maximum across overlapping patterns/prefixes, additive only across disjoint lengths), while dependent lookup uses it as a fiber witness. Length compatibility alone only proves a possible match. |
| Conditional guard | Mutually exclusive empty/nonempty branches retain `ifZero` instead of being independently added. |
| Scalar reduction | Z3-backed total-size and path-length bounds reduce the spatial product from annotated atom envelopes only; opaque atoms are never measured by evaluation. Reduction may tighten but may not change concretization. |
| Solver degradation | `estimateReported`/`outputReported` return structured timeout, unknown, nonzero-exit, and I/O diagnostics with the compositional fallback. Timeouts are reported when they fire; a missing Z3 executable is a hard configuration error. |
| Group-sensitive iteration | Constant heads contribute at most one nonempty group; affine heads are capped by their declared domain; unknown heads by source size. A constant-headed tail is the whole matching stratum. |
| Pointwise iterator chain | A canonical nested iterator chain consuming one complete source path has upper `source size * leaf-per-path upper`, avoiding independent regrouping products. The scalar transfer propagates the same cap through nested maps and fixed-path wrappers, and an injective reconstruction arm preserves the headed-source lower bound. |
| Total source caps | Selectors cannot exceed their source; composition cannot exceed the product of operand totals. These caps reduce stratum-derived totals. |
| Semantic type annotation | `SpatialRoutineAnnotations.resultLaws` contributes a proved must/may cardinality envelope. It is an analysis input and is intersected with, never substituted for, constructor analysis. |
| Finite relational count | `FiniteIntConstraintProblem` counts assignments within an explicit node budget and falls back to no refinement when exhausted. |
| Fiber degree | Exact constants are counted directly. Symbolic key lower bounds use suffix capacity; min/max fiber bounds combine key intervals, total edges, and maximum suffix capacity. A direct `relation(head)` iterator consumes these bounds and quantitative coverage without assuming selected suffix fibers are disjoint. Arbitrary key-specific correlation remains future work. |
| Bounded representation | Above the pattern limit, patterns are summarized into length strata. Summarization enlarges concretization; it never truncates alternatives. |
| Inconsistent state | `SpatialType.bottom` represents contradictory evidence and absorbs meet and deterministic transfer. |
| Fixpoint invariant | Ascending iteration plus checked widening returns only a post-fixpoint; failure to establish one returns top in every spatial component. |
| Analysis cost | Symbolic lower/upper work/allocation/round intervals are propagated by one model per executor. Iteration and fixpoint are charged; decreasing recursion closes to executable `additive * geomSeries(branching,rounds)`, with exact constant evaluation and a dominant-order projection. |
| Decorated tree | Every occurrence has a positional child-index identity; repeated lexical observations are retained and joined for optimizer consumers. |

## Semantic interval lattice

Let `Path` be the set of paths and `Space = P(Path)`. The semantic envelope of a spatial type is

```text
A = {⊥} + {[L,U] | L ⊆ U ⊆ Path}
```

with concretization

```text
γ(⊥)     = ∅
γ([L,U]) = {S | L ⊆ S ⊆ U}.
```

The precision order is inclusion of concretizations:

```text
A ⊑ B  iff  γ(A) ⊆ γ(B)
[L₁,U₁] ⊑ [L₂,U₂]  iff  L₂ ⊆ L₁ and U₁ ⊆ U₂.
```

Thus `⊥` admits no concrete space, while `⊤ = [∅,Path]` admits every space. Exact abstraction is `[S,S]` and has the singleton concretization `{S}`.

For a nonempty family of non-bottom intervals:

```text
supᵢ [Lᵢ,Uᵢ] = [intersectionᵢ Lᵢ, unionᵢ Uᵢ]
infᵢ [Lᵢ,Uᵢ] = normalize([unionᵢ Lᵢ, intersectionᵢ Uᵢ])
```

where an inconsistent interval normalizes to `⊥`. Bottom is ignored by a supremum and absorbs an infimum. The empty supremum is `⊥`; the empty infimum is `⊤`. Binary join and meet are the supremum and infimum of a pair. This is a complete bounded lattice and satisfies partial-order, universal-bound, idempotence, commutativity, associativity, and absorption laws.

`SpatialType.joinAlternatives` is this lattice join. It is not the MORKL
set-union transfer: the former combines alternative abstract states by taking
the least common envelope, while the latter maps two simultaneously present
operand sets through concrete union. Swapping them is generally unsound even
though both functions combine two `SpatialType` values.

It is **not distributive**. Normalization can turn an inconsistent meet into bottom, and both distributive equalities have finite counterexamples. Optimizers and reductions must not assume distributivity of abstract types even though concrete path sets form a Boolean algebra.

## Reduced product

The implementation is a finite projection of this model. Its intended semantic interpretation is a reduced product:

```text
γᵣ(strata × trie-shape × size × length × dependencies)
  = γstrata ∩ γtrie-shape ∩ γsize ∩ γlength ∩ γdependencies.
```

Componentwise refinement is monotone in the product order. `SpatialType.reduce`
clamps strata by totals, projects strata back to total/length components,
detects constant contradictions (including required disjoint strata and a
positive scalar lower bound with no possible stratum), and iterates to an
idempotent result. The FOL
obligations abstract non-shape components behind `qgamma`; they specify the
target property rather than verify this Scala reduction.

A semantic contract can equivalently contribute a must-set `C_L` and may-set
`C_U`. Its interval reduction is

```text
contract([L,U], C_L, C_U) = normalize([L union C_L, U intersection C_U]).
```

If `L subset S subset U` and `C_L subset S subset C_U`, the reduced interval
still contains `S`. It always refines `[L,U]`; strengthening either side of a
consistent contract refines the result again (an inconsistent interval
normalizes to bottom in the executable lattice). These three statements are
standalone FOL obligations. Cardinality contracts in the implementation are
the arithmetic projection of this theorem.

The concrete semantic laws currently used at cornerstone boundaries are:

| Contract | Required semantic precondition | Cardinality consequence |
| --- | --- | --- |
| subset of an `m`-image of `X` | every output has an input witness and each input has at most `m` outputs | `upper <= m*upper(X)` |
| contains `X` | every input path occurs in the result | `lower >= lower(X)` |
| directed transitive closure of `E` distinct edges | direct edges retained; outputs are reachable ordered endpoint pairs | `E <= result <= E^2` |
| finite universe `U` | every output is a member of `U` | `upper <= |U|` |
| connected finite component | every nonempty legal seed saturates the named component | exact zero for empty seed, otherwise component capacity |
| width-parameterized sliding-puzzle reachability | legal moves preserve permutation parity and the annotated seed lies in the connected component | exact zero for empty seed, otherwise `(width²)!/2` (one for width 1) |
| divide-and-conquer SCC representatives | each non-singleton component emits one representative/member pair for every non-representative node; all nodes are edge endpoints | `0 <= result <= 2E` |
| finite constraint solutions | finite variable domains and relational constraints are part of the input annotation | exact abstract constraint count |
| parameterized n-queens | production all-different and diagonal constraints for board size `n` | exact constraint count within the node budget |

These are explicit boundary annotations. Exact consequences are intersected
with structural intervals and produce bottom on contradiction. There is no raw exact-cardinality law,
so an observed result size cannot be fed back as an unexplained bound. The
generic analyzer does not infer a
graph closure, legal puzzle state, or queens constraint merely from an
unrelated syntax tree.

## Best interval transformers

For valid input intervals `A=[L₁,U₁]` and `B=[L₂,U₂]`, the following are sound. Union and subtraction are additionally proved to be the best correct interval abstractions, not merely safe envelopes.

| MORKL operation | Abstract interval |
| --- | --- |
| `A ∪ B` | `[L₁ ∪ L₂, U₁ ∪ U₂]` |
| `A ∩ B` | `[L₁ ∩ L₂, U₁ ∩ U₂]` |
| `A \ B` | `[L₁ \ U₂, U₁ \ L₂]` |
| `A x B` | `[L₁ x L₂, U₁ x U₂]` |
| `A <| B` | `[L₁ <| L₂, U₁ <| U₂]` |
| raffination | `[L₁ raff U₂, U₁ raff L₂]` because the prefix operand is antitone |
| wrap/unwrap by fixed prefix | Apply the operation to both bounds |
| tails union, prefix closure, suffix closure, tails closure | Apply the monotone operation to both bounds |
| tails intersection | `[∅, tailsUnion(U)]`; adding a head can shrink a universal tails meet |
| ordered range | `[∅,U]` generally; finite rank windows/suffixes are additionally capped by their source-independent width, full sentinel is identity, and a statically empty range is exact empty |

The product, restriction, and closure formulas rely on concrete monotonicity. Raffination and subtraction are monotone in the left operand and antitone in the right operand.

`Range` is not monotone under source inclusion: inserting an earlier path changes rank-based selection. An arbitrary iteration body is also not monotone because it may subtract or inspect a changing bound tail. If the template is monotone in its tail argument, however, source iteration is monotone and `[Iter(L,F), Iter(U,F)]` is sound. This positivity condition is proved explicitly rather than silently assumed.

## FOL model obligations

The generated `spatial_*_fo.p` obligations cover:

- closed-form interval order, partial order, bottom/top, and exact concretization;
- arbitrary supremum/infimum contracts, binary upper/lower bounds, least/greatest universal properties, interval consistency, and all bounded-lattice algebra laws;
- concrete and abstract monotonicity/variance for composition, restriction, raffination, and positive iteration;
- transfer soundness for union, intersection, subtraction, composition, restriction, raffination, wrap, unwrap, closures, safe range, universal tails intersection, and positive iteration;
- best-correctness for union and subtraction;
- reduced-product projection, componentwise monotonicity, gamma preservation, and reduction idempotence.
- semantic-contract transfer soundness, refinement, and monotonicity under a stronger contract.
- structural interpreter soundness from the finite-AST induction principle and constructor-transfer premises;
- post-fixpoint induction for `Fixpoint` and optimizer soundness transported across evaluator-preserving rewrites;
- backend-selection bridges: bounded-depth trie unrolling, common-prefix zipper pre-focus, and exact graph constant folding, each derived from extensional backend semantics.

Each generated problem has a lean, operator-specific prelude. Abstract values and abstract collections are guarded by predicates because TPTP FOL is untyped. Transformer equations are guarded by `L ⊆ U`; without that guard, different invalid interval representatives all denote bottom but could be mapped to different outputs, making the theory inconsistent.

`SpatialLawRegistry` maps law names to their generated certificates and an
explicit `Proved` or `Refuted` verdict. Refuted claims retain both a committed
finite witness and an expected-`sat` bounded Z3 obligation. Current negative
entries include right-union distribution of subtraction and commutativity of
restriction; failed conjectures therefore remain visible in the proof story.

`FiniteSpatialTypeBridge` owns the canonical bottom-plus-28-value embedding
boundary over a three-element universe: exact singleton strata use `[1,1]` for
must members and `[0,1]` for may-only members, while decoding rejects every
noncanonical shape, bound, duplicate, scalar, length, or cost observation.
`SpatialTypeLatticeTest` shares that production boundary with an independent
set oracle and exhaustively checks `reduce`, `lessOrEqual`,
`joinAlternatives`, and `meet` for all values and all 784 ordered pairs. A
direct inconsistent scalar/strata case also guards reduction.

The core proof generator independently invokes those four live production
methods, fail-closed decodes their 2,380 observations, and emits
`spatial_type_finite_code_bridge.smt2`. Its SMT layer defines normalization,
order, join, and meet directly over three-bit must/may masks and asserts the
disjunction of every possible production/semantic mismatch; `unsat` is the
bounded refinement theorem. The companion
`bad_spatial_type_finite_code_bridge_flipped_output_generated_negative_control.smt2`
flips exactly `lessOrEqual(bottom,bottom)` and must be `sat`, proving that the
query detects a corrupted production table. This code-connected theorem
exposed and now guards required-stratum/disjoint-pattern and empty-strata
contradictions. Its scope is the complete 28-value quotient, not a general JVM
representation-isomorphism proof.

Executable semantic checks complement FOL where cardinality arithmetic is not
encoded: all 512 three-node directed graphs satisfy `E <= |TC(E)| <= E^2` and
the divide-and-conquer SCC representative output stays within `2E`; all 512 subsets of a 3x3 Life field
satisfy the nine-image law; and the production finite-constraint component
matches n-queens counts through size six. These checks run after abstract
interpretation and have no data path back into its annotations.

## Remaining implementation-refinement obligations

The complete lattice makes the following future obligations well-formed rather than ad hoc:

1. Connect the generic constructor-soundness and fixpoint bridge theories to the concrete Scala `analyze` implementation by a checked refinement/extraction layer. The semantic theorem `eval(e,ρ) ∈ γ(analyze(e,ρ#))` is now stated at the FOL boundary and audited over original and optimized random programs, but source-to-theory correspondence remains trusted.
2. Assumption refinement: refining every input type must refine output for positive programs; variance annotations identify the exact exceptions.
3. Strengthen the current post-fixpoint induction obligation to a leastness theorem for positive `Fixpoint` over the full represented stratum product.
4. Best-correctness for intersection, product, restriction, raffination, closures, and positive iteration.
5. A Galois insertion for the finite pattern/stratum representation, including a proof that cap-based summarization is an upper closure operator.
6. Concrete cardinality/length reduction coherence, replacing generic `qgamma` with arithmetic theories and proving every reduction step preserves gamma.
7. Generalize the current quantitative prefix coverage, symbolic fiber bounds,
   and direct dependent-lookup transfer to key-correlated degree maps that
   participate in the same product order and fixpoint induction.
