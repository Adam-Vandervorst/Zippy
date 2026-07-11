# Valued Track Learnings For The Unit Track

The value experiment is staying separate, but it exposed several ways to make
the path-set implementation stronger.

## Laws To Exploit More Aggressively

- Treat path sets as the primary algebra.  Do not accidentally generalize core
  laws to path-keyed maps; set union/intersection/diff have stronger identities.
- Use idempotence everywhere: `A \/ A = A`, `A /\ A = A`, `A \ A = empty`.
  These are unconditional for unit paths and should be cheap optimizer rules.
- Use subset absorption as a first-class unit law: when `B <= A`, rewrite
  `A \/ B` to `A` and `A /\ B` to `B`.  The current unit optimizer recognizes
  conservative syntactic subset forms for `Range`, `Restriction`, `Raffination`,
  `Subtraction`, `Intersection`, and `Union`.
- Use complement laws that are only membership-sensitive in the unit track:
  `(A /\ B) \ A = empty`, `(A \/ B) \ A = B \ A`,
  `A \ (A /\ B) = A \ B`, `(A \ B) \ B = A \ B`,
  `(A \ B) \/ B = A \/ B`, `(A \ B) \/ (A /\ B) = A`,
  `A \ (A \ B) = A /\ B`, `A \ (B \ A) = A`,
  `(A \/ B) \ (A \ B) = B`,
  `A \ Restriction(A, P) = Raffination(A, P)`, and
  `A \ Raffination(A, P) = Restriction(A, P)`.
- Use common-factor laws when they reduce expression size:
  `(A /\ B) \/ (A /\ C) = A /\ (B \/ C)`,
  `(A \/ B) /\ (A \/ C) = A \/ (B /\ C)`,
  `(A \ B) \/ (A \ C) = A \ (B /\ C)`, and
  `(A \ B) /\ (A \ C) = A \ (B \/ C)`.  These are clean unit-set laws; a valued
  map must prove that common payloads are not changed by the chosen join/meet
  lattice before using the same rewrites.
- Fuse same-source prefix filters in the unit track:
  `Restriction(A, P) \/ Restriction(A, Q) = Restriction(A, P \/ Q)` and
  `Raffination(A, P) /\ Raffination(A, Q) = Raffination(A, P \/ Q)`.  These are
  just membership partitions for path sets.  In a valued map, the same shapes
  require idempotent payload merge/meet and proof that both sides preserve the
  source payload for every retained path.
- Treat closure containment as a unit-set absorption source, but keep the
  epsilon semantics precise: `A \ {epsilon} <= PrefixClosure(A)`, `A \
  {epsilon} <= SuffixClosure(A)`, `A <= TailsClosure(A)`, `SuffixClosure(A) <=
  TailsClosure(A)`, and `TailsUnion(A) <= TailsClosure(A)`.  This gives cheap
  optimizer wins without any payload aggregation obligations, while preserving
  MORKL's choice that prefix/suffix closures of an epsilon path are empty.
- Keep the subset relation membership-only.  Do not lift these rewrites to
  valued maps unless the payload side proves that merging or meeting an
  included payload leaves the outer payload unchanged.
- Prefer membership equivalences over payload-bearing equivalences in proofs.
  The unit track can avoid functional-map side conditions entirely.
- Keep subtraction exact.  A path-set difference has negative information at the
  path level; it does not need payload-existence witnesses or merge semantics.
- Strengthen closure/frontier proofs around derivatives and membership.  Unit
  paths let the closure scheduler reason about "is this suffix present" without
  considering value aggregation.

## Runtime Lessons

- Keep the referential-identity fast paths.  They are even cleaner for unit
  tries: union/intersection can instantly accept identical operands; diff can
  instantly return empty.
- Push operations into the trie frontier.  The value oracle showed how quickly
  `encodedEntries` folds become a crutch; unit operations should stay trie-local
  and ordered-border-local.
- Make every operation own its native `IntMap` traversal.  Avoid "lookup then
  iterate" shapes where a single Patricia-aware callback can do the job.
- Keep ordered child arrays or cached ordered views only where an ordered
  operation actually needs them.  Range and sibling movement benefit; ordinary
  union/intersection/diff should stay map-native.
- Separate concrete cursor movement from virtual zippers.  A concrete
  focus/context zipper is useful for edit/path/plug tests, while the evaluator
  should remain a virtual algebra over operations.

## Proof Lessons

- Side conditions multiply fast once values exist.  The unit proof layer should
  stay intentionally payload-free so Vampire/Z3 obligations are smaller and
  stronger.
- Generated artifacts need one source of truth.  The sidecar currently has
  historical valued proof artifacts; before values advance, it needs its own
  generator so snapshots cannot drift.
- Keep acceptance gates about what the main track actually claims.  Value
  payload checks should never appear as production proof rows unless production
  MORKL supports payloads end to end.
- Negative/key observations are simpler as unit predicates.  Preserve the
  current relational absence model instead of lifting it to valued maps early.
- If a law is true only because `join` or `meet` is commutative/idempotent, it
  belongs in the valued sidecar, not in the unit optimizer.

## Benchmark And Reporting Lessons

- Report payload work as an independent track.  Combining unit and valued
  numbers would make speedup attribution muddy.
- Keep fallback notes precise.  "Path-set production runtime" is a design
  choice, not a missing valued feature.
- Do not let richer semantics weaken the publication path.  Values can be a
  future generalization, but the supercompiler should first be excellent for
  the more lawful path-set language.
