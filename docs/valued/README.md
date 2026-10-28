# Valued Path-Map Track

This directory is a sidecar experiment for terminal payloads on trie paths.  The
production MORKL runtime remains a set of paths, not a path-keyed map.  The main
codebase must compile and run with this `valued/` directory removed.

## Why This Is Separate

Path sets have stronger laws than path-keyed maps:

- Union and intersection are idempotent without consulting a payload lattice.
- Subtraction is ordinary set difference, not "left payload survives if the
  right side lacks any payload at the same path."
- Subset absorption is unconditional: if `B <= A`, then `A \/ B = A` and
  `A /\ B = B`.  In a path-keyed map this would require payload agreement or
  idempotent merge side conditions.
- Closure, frontier, and Range proofs can reason over membership only.
- Optimizer laws do not need side conditions about `join`/`meet` consistency,
  payload determinism, or value merge commutativity.

Those stronger laws are the current publication track.  Values are useful, but
they should not weaken or complicate the unit semantics until the payload track
has its own proof and benchmark story.

## Unit-Track Laws Already Imported

The main source optimizer now uses a conservative syntactic subset relation over
unit path sets.  It absorbs terms such as:

- `A \/ (A /\ B) => A`
- `A /\ (A \/ B) => A`
- `A \/ (A \ B) => A`
- `(A \ B) \/ B => A \/ B`
- `(A \ B) \/ (A /\ B) => A`
- `A /\ (A \ B) => A \ B`
- `(A /\ B) \ A => empty`
- `(A /\ B) \/ (A /\ C) => A /\ (B \/ C)` for common-factor intersections
- `(A \/ B) /\ (A \/ C) => A \/ (B /\ C)` for common-factor unions
- `(A \ B) \/ (A \ C) => A \ (B /\ C)`
- `(A \ B) /\ (A \ C) => A \ (B \/ C)`
- `Restriction(A, P) \/ Restriction(A, Q) => Restriction(A, P \/ Q)`
- `Raffination(A, P) /\ Raffination(A, Q) => Raffination(A, P \/ Q)`
- `(A \/ B) \ A => B \ A`
- `A \ (A /\ B) => A \ B`
- `A \ (A \ B) => A /\ B`
- `A \ (B \ A) => A`
- `(A \/ B) \ (A \ B) => B`
- `(A \ B) \ B => A \ B`
- `A \/ Restriction(A, P) => A`
- `A /\ Restriction(A, P) => Restriction(A, P)`
- `A \ Restriction(A, P) => Raffination(A, P)`
- `A \ Raffination(A, P) => Restriction(A, P)`
- `Restriction(A, P) /\ Raffination(A, P) => empty`
- analogous `Range(A, ...)` and `Raffination(A, P)` subset forms
- `A \ {epsilon}` absorbs into `PrefixClosure(A)` and `SuffixClosure(A)`;
  plain `A` does not, because MORKL prefix/suffix closures do not include
  epsilon just because `A` contains epsilon
- `A`, `TailsUnion(A)`, and `SuffixClosure(A)` absorb into `TailsClosure(A)`
  where the unit membership semantics makes that immediate

These rewrites intentionally live in the unit track only.  A valued map could
make the same shape true only after proving the relevant payload lattice laws.

## What Is Here

- `../../valued/src/main/scala/morkl/valued/ValuedTrieSpace.scala`
  - `MergeLattice[V]`
  - `ValuedTrieSpace[V]` over `IntMap` children and optional terminal payloads
  - native union/intersection/diff/product/restriction/raffination/wrap/unwrap,
    tails, head, and closure operations
  - a direct `ValuedSpace[V]` expression evaluator
  - a concrete focus/context zipper with down/up/sibling/edit operations
- `../../valued/src/test/scala/morkl/valued/ValuedTrieSpaceTest.scala`
  - oracle tests for lattice merge behavior
  - structural operation tests
  - direct evaluator dispatch tests
  - focus/context movement and edit tests
- `../../valued/proofs/vampire/generated/valued_*.p`
  - historical TPTP artifacts for valued membership and backend equivalence
- `../../valued/proofs/generated/egg/valued_backend_rewrite_equivalence.egg`
  - historical egg normalization certificate for valued backend surfaces
- `ValuedLearnings.md`
  - lessons from this side track that should strengthen the unit/path-set track

## What Needs To Be Added Still

- A sidecar proof generator.  The checked-in valued TPTP/egg files are a
  snapshot; the main `ProofArtifacts.scala` intentionally no longer emits them.
- A sidecar runner that validates only `valued/` artifacts and never gates the
  unit path-set proof pipeline.
- A payload-aware fuzzer with generated valued programs, argument maps, result
  maps, and shrinking.
- A real valued zipper algebra.  The current zipper is a concrete
  focus/context trie cursor; it is not yet the full virtual zipper stack used by
  the unit track.
- Efficient valued trie operations.  Some operations still use `encodedEntries`
  folds as an oracle-style implementation rather than fully trie-local
  algorithms.
- Benchmarks comparing payload-map behavior against the unit path-set runtime.
- A clear payload-lattice law contract for every optimizer law before any value
  operation is allowed back into production MORKL.

## How To Compile The Sidecar

From the repository root:

```bash
env _JAVA_OPTIONS='-Xmx1536m -Xss64m' scala-cli test valued src/main/scala --server=false --scala 3.8.1 --source 3.3 --dependency org.scalameta::munit:1.2.1 --dependency org.scala-lang.modules::scala-collection-contrib:0.3.0
```

The main track should also compile after deleting this directory:

```bash
env _JAVA_OPTIONS='-Xmx1536m -Xss64m' scala-cli test src/main/scala src/test/scala --server=false --scala 3.8.1 --source 3.3 --dependency org.scalameta::munit:1.2.1 --dependency org.scala-lang.modules::scala-collection-contrib:0.3.0
```
