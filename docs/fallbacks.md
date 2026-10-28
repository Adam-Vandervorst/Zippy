# MORKL Fallback Inventory

This is a current-state audit of implementation paths that deliberately fall back to a less-specialized evaluator, materialization step, shared proof predicate, or unsupported marker. These are not all bugs, but each one must be visible before benchmark or proof claims are treated as publication-grade.

## Runtime / Evaluation

- `src/main/scala/ZipperSpace.scala`: `transpileZ` automatically lowers union-saturating single and mutual recursive helpers to zipper fixpoints. Structurally positive/productive steps use prefix demand; lowered steps outside that runtime admission use the lazy exact synchronous representation described below. Recursive calls outside the proved helper-lowering fragment still fail explicitly with `UnsupportedOperationException`; they never fall back to `evalTrie`.
- `src/main/scala/ZipperSpace.scala`: source `Space.Fixpoint` uses shared prefix cells only after a structural positivity/productivity check. Union, intersection, composition, restriction, and causal wrapping are admitted; state-dependent generic iteration, `Range`, `TailsIntersection`, `Unwrap`, generic tail/prefix/suffix closures, negative subtraction/raffination operands, folds, nested fixpoints, calls, and host callbacks use a lazy exact synchronous boundary. Prefix navigation remains lazy, but the first terminal/frontier observation performs global Kleene rounds; when path and space contexts are materializable maps, those inherently global rounds execute directly in native `TrieSpace` algebra rather than rebuilding virtual cursor trees. The bounded `{a,b}` / `Literal(x.z) \/ TailsIntersection(state)`, `{a}` / `Unwrap(state,a)`, union-wrapped tail, and tail-emitting iteration regressions record the transient and unbounded-lookahead boundaries.
- `src/main/scala/ZipperSpace.scala`: the recognized `RangeTail` form also retains its exact synchronous materialized fallback. `Range` is non-monotone as its input grows, so a prefix first demanded in a later approximation cannot safely reconstruct a transient earlier selection. The bounded `{a.b,b.a}` / `Range(0,1)` oracle regression records this specialized boundary.
- `src/main/scala/ZipperSpace.scala`: demand-fixpoint cells retain monotone observations, while each solver round freezes the preceding approximation and rebuilds the step with fresh cursor wrappers. This prevents cached iteration frontiers from surviving into later state versions.
- `src/main/scala/ZipperSpace.scala`: direct `SpaceZipper.fixpoint` rejects potentially length-growing prefixed templates with `UnsupportedOperationException`. `transpileZ` currently does not emit these tags for source `Space.Fixpoint`; this direct API path remains an explicit unsupported marker.
- `src/main/scala/ZipperSpace.scala`: generic `Space.Iteration` templates that do not match a known template are represented as lazy branch-cached virtual iterations. The old materialized `genericJoined` fallback is gone; both direct `child(k)` observations and `childrenIterator` now reuse a per-key virtual child cache.
- `src/main/scala/ZipperSpace.scala`: grounded path/space functions (`GroundedPP`, `GroundedSP`, `GroundedPS`, `GroundedSS`) necessarily cross through host Scala functions and may materialize `SpaceValue`.
- `src/main/scala/TrieSpace.scala`: grounded path/space functions still materialize/decode at the trie boundary because their semantics are host callbacks.

## Graph / Exec

- `src/main/scala/MORKL.scala`: operation-graph serialization rejects grounded host callbacks (`Path.GroundedPP`, `Path.GroundedSP`, `Space.GroundedPS`, `Space.GroundedSS`) instead of silently pretending they are graph-native.
- `src/main/scala/MORKL.scala`: graph compilation records unsupported backend nodes and reports graph backend failure instead of manufacturing a graph result.
- `src/main/scala/MORKL.scala`: exec fallback calls are still possible for unproved or intentionally retained routine calls; they must remain visible in benchmark fallback notes.

## Formal / Proof

- `proofs/PROOF_REPORT.md`: the operational manifest currently has zero `UNPROVED` rows, but some rows are `proved-bounded` through mixed/bounded evidence rather than unbounded FOL proofs.
- `proofs/PROOF_REPORT.md`: `Fold` and grounded host functions remain represented by shared structural predicates in the axiomatized full-program FOL schema tier. That tier checks contract consistency, not implementation correctness, and those predicates are not yet unfolded into op-specific independent proof lemmas.
- `proofs/PROOF_REPORT.md`: the unbounded bisimulation proof for the complete demand-driven Antimirov frontier scheduler is not complete; current closure/frontier evidence combines bounded SMT, egg witnesses, and named FOL bridge obligations.
- `zipper-descend.egg`: broad ordered-key `Range` schedulers that caused e-graph blowup are intentionally not used in the main model. Range uses focused ordered border-state relations and generated witnesses instead.

## Recently Removed

- `TrieSpace.head` no longer reconstructs singleton encoded paths through `fromEncodedPaths`; it now builds the shallow trie directly from the child map.
- `SpaceZipper.Head.concrete` no longer duplicates that old encoded-path reconstruction and delegates to `TrieSpace.head`.
