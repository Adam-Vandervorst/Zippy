# MORKL Fallback Inventory

This is a current-state audit of implementation paths that deliberately fall back to a less-specialized evaluator, materialization step, shared proof predicate, or unsupported marker. These are not all bugs, but each one must be visible before benchmark or proof claims are treated as publication-grade.

## Runtime / Evaluation

- `src/main/scala/ZipperSpace.scala`: `transpileZ` now rejects top-level self-recursive union call shapes with `UnsupportedOperationException` instead of falling back to materialized `evalTrie`. This keeps unsupported recursive zipper execution visible until a sound zipper-local lowering exists.
- `src/main/scala/ZipperSpace.scala`: generic `Space.Fixpoint` without a recognized safe iteration template still runs a materialized saturating trie loop. This is the honest fallback for unproved recursion; it accumulates `current ∪ step(current)` and does not use a convergence cap.
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
- `proofs/PROOF_REPORT.md`: `Fold` and grounded host functions remain represented by shared structural predicates in the full-program FOL tier. They are correctness-gated, but not yet unfolded into op-specific proof lemmas.
- `proofs/PROOF_REPORT.md`: the unbounded bisimulation proof for the complete demand-driven Antimirov frontier scheduler is not complete; current closure/frontier evidence combines bounded SMT, egg witnesses, and named FOL bridge obligations.
- `zipper-descend.egg`: broad ordered-key `Range` schedulers that caused e-graph blowup are intentionally not used in the main model. Range uses focused ordered border-state relations and generated witnesses instead.

## Recently Removed

- `TrieSpace.head` no longer reconstructs singleton encoded paths through `fromEncodedPaths`; it now builds the shallow trie directly from the child map.
- `SpaceZipper.Head.concrete` no longer duplicates that old encoded-path reconstruction and delegates to `TrieSpace.head`.
