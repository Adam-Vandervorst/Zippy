# Proof Pipeline Report

Status: PASS_WITH_PROOF_DEBT

## Scope

- Scala is the source of truth for generated proof and example egg artifacts.
- `morkl.ProofArtifactGeneratorMain` generates SMT2 and TPTP files plus `proofs/proof_manifest.tsv`.
- `morkl.generateZipperEggTests` generates the shared-prelude `formal.egg` and `zipper.egg` introductions plus the independent `zipper-egg-tests/*.egg` examples.
- `morkl.generateCornerstoneProofArtifacts` generates exact-output SMT2/TPTP/egg certificates for aunt, semi-naive datalog, GOL, 15-puzzle, temperature, and n-queens.
- `morkl.generateOpenProgramProofArtifacts` generates open-program SMT2 equivalence obligations over symbolic bounded input spaces plus structural full-program TPTP obligations.
- The runner emits `proofs/operational_rule_manifest.tsv` by scanning every operational `(rewrite ...)` and `(rule ...)` in `zipper-descend.egg`, mapping semantic rows to proof artifacts where known, mapping path normalizers, memo/cache wrappers, and scheduler-observability helpers to explicit FOL contracts where available, keeping any remaining relational frontier/key scheduling helpers as `axiom-elsewhere`, and marking missing semantic coverage as `UNPROVED`.
- This Python script runs external solvers/checkers against the Scala-generated artifacts and curated termination artifacts.
- Operational proof debt in this report: `433` proved-bounded rows, `0` axiom-elsewhere rows, and `0` UNPROVED rows. A zero-UNPROVED report is not the same as a fully unbounded proof.
- Vampire runs in portfolio mode and proves first-order equivalence obligations connecting zipper membership, eager trie membership, and path-set membership. Iteration is represented as a general head/rest binder with arbitrary template-expression DAGs; body-union distribution, guarded invariant motion, and wrap/product/intersection/diff/restriction hoists have unbounded FOL obligations in addition to bounded counterexample checks.
- TailsIntersection has an arbitrary-cardinality closed-frontier refinement theorem. The generated `tails-intersection-frontier.egg` artifact executes the corresponding demand-built key-list fold over a nested virtual union with a repeated head, demonstrating that same-head children merge before the all-head meet.
- Core unit path-set algebra now has unbounded FOL obligations for union/intersection idempotence and associativity, diff self/union-right, child intersection/diff, restriction/raffination partition/disjointness, path concat epsilon normalization, memo/cache identity, and ordered Range child-border soundness/pruning facts. Operational rows that still cite bounded fixture-specific laws remain `proved-bounded` by weakest-tier accounting.
- Bounded universe: alphabet `a,b`, max path length `3`, `15` paths.
- Valid laws are checked by asking Z3 for a counterexample to equality; `unsat` means no bounded counterexample was found.  The bounded law table includes MORKL-style Iteration with head/rest bindings.
- Product/concatenation derivative laws are guarded by the principle `no concatenation escapes the bounded universe`: `child_product_*` uses a generated `ProductClosed(X,Y)` assumption that forbids exactly those X/Y path pairs whose concatenation would fall outside the bounded universe. Both `a` and `b` child representatives are checked, and the unguarded mutation must be `sat`.
- Cornerstone example certificates are exact closed-program output equivalence checks generated from Scala after Scala has checked the compared evaluators/executors agree.
- Open-program SMT certificates compare expanded source, source optimization, raw graph round-trip, and optimized graph round-trip for all symbolic inputs in each generated bounded universe.
- Structural full-program FOL certificates emit generated MORKL program DAGs for Aunt, semi-naive Datalog, GOL, temperature, 2x2 sliding puzzle, the complete 24-state 2x2 sliding-puzzle step, and 4-queens, then prove source, optimized-source, trie, zipper, and graph backends equivalent using constructor-specific implementation lemmas over arbitrary input-space interpretations. `Iter` is modeled with an explicit path/space binding environment; `Range` is modeled as source membership plus ordered rank/bounds selection.
- `terminating/` carries hand-staged termination and least-fixpoint artifacts: Vampire-checkable least-fixpoint uniqueness and finite-growth decrease lemmas, Z3-checkable no-infinite-descent induction steps, egglog sketches, and Datalog/transitive termination/equivalence obligations. These artifacts are executed by the corresponding gate unless that gate is skipped.
- Arbitrary-data backend obligations use symbolic input spaces/templates to prove source, trie, zipper, and graph constructors agree independently of the concrete example data.
- Negative controls are intentionally false laws; they must return `sat`.
- Vampire: available at `/Applications/Vampire`
- Per-obligation solver budgets: Z3 `300s`, Vampire `300s`; solver obligations run with up to `1` workers.

## Scala Generation Gate

| Step | Expected | Actual | Result |
| --- | --- | --- | --- |
| `product-guard artifact invariant` | `ProductClosed+negative-control` | `ok` | PASS |
| `negative-control family invariant` | `all-families-sat` | `ok` | PASS |
| `symbol-coverage invariant` | `both-symbols-or-symmetry` | `ok` | PASS |
| `negative/key acceptance invariant` | `relational-absence+keyset-noncollapse` | `ok` | PASS |
| `concrete closure rewrite invariant` | `no-concrete-closure-rewrites` | `ok` | PASS |
| `frontier algebra rule invariant` | `required-tail-frontier-and-state-rules` | `ok` | PASS |
| `iter/fixpoint acceptance invariant` | `binary-iter-fixpoint+datalog-zipper-tier` | `ok` | PASS |
| `context movement acceptance invariant` | `focus-context+plug-path-sibling` | `ok` | PASS |
| `executable zipper context invariant` | `path-plug-edit-sibling-oracles` | `ok` | PASS |
| `transform replacement invariant` | `Space.Transform-absent+pure-Unification.T` | `ok` | PASS |
| `termination proof artifact invariant` | `solver-runnable least-fixpoint+finite-growth+descent` | `ok` | PASS |
| `Range acceptance invariant` | `ordered-border-state+generated-artifacts` | `ok` | PASS |
| `operational rule manifest generation` | `exit-0` | `exit-0` | PASS |
| `operational manifest closure and proof-debt accounting` | `0-UNPROVED with proof-debt surfaced` | `0-UNPROVED; 433-proof-debt` | PASS |
| `scala egg artifact generation` | `exit-0` | `exit-0` | PASS |

## Vampire Equivalence Gate

| Obligation | Expected | Actual | Result | Artifact |
| --- | --- | --- | --- | --- |
| `trie_set_member_depth_0` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/trie_set_member_depth_0.p` |
| `trie_set_member_depth_1` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/trie_set_member_depth_1.p` |
| `trie_set_member_depth_2` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/trie_set_member_depth_2.p` |
| `trie_set_member_depth_3` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/trie_set_member_depth_3.p` |
| `trie_set_member_depth_4` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/trie_set_member_depth_4.p` |
| `zipper_trie_member_depth_0` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_trie_member_depth_0.p` |
| `zipper_trie_member_depth_1` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_trie_member_depth_1.p` |
| `zipper_trie_member_depth_2` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_trie_member_depth_2.p` |
| `zipper_trie_member_depth_3` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_trie_member_depth_3.p` |
| `zipper_trie_member_depth_4` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_trie_member_depth_4.p` |
| `eager_union_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_union_set_equiv.p` |
| `eager_intersection_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_intersection_set_equiv.p` |
| `eager_diff_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_diff_set_equiv.p` |
| `path_concat_epsilon_left_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/path_concat_epsilon_left_fo.p` |
| `path_concat_epsilon_right_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/path_concat_epsilon_right_fo.p` |
| `set_union_idempotent_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_union_idempotent_fo.p` |
| `set_union_associative_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_union_associative_fo.p` |
| `set_intersection_idempotent_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_intersection_idempotent_fo.p` |
| `set_intersection_associative_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_intersection_associative_fo.p` |
| `set_diff_self_empty_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_diff_self_empty_fo.p` |
| `set_diff_union_rhs_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_diff_union_rhs_fo.p` |
| `set_child_intersection_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_intersection_fo.p` |
| `set_child_diff_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_diff_fo.p` |
| `set_restriction_raffination_partition_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_restriction_raffination_partition_fo.p` |
| `set_restriction_raffination_disjoint_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_restriction_raffination_disjoint_fo.p` |
| `keyset_union_empty_left_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_union_empty_left_fo.p` |
| `keyset_union_empty_right_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_union_empty_right_fo.p` |
| `keyset_union_idempotent_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_union_idempotent_fo.p` |
| `keyset_intersection_empty_left_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_intersection_empty_left_fo.p` |
| `keyset_intersection_empty_right_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_intersection_empty_right_fo.p` |
| `keyset_intersection_idempotent_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_intersection_idempotent_fo.p` |
| `keyset_intersection_one_hit_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_intersection_one_hit_fo.p` |
| `keyset_intersection_one_miss_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_intersection_one_miss_fo.p` |
| `keyset_diff_empty_left_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_diff_empty_left_fo.p` |
| `keyset_diff_empty_right_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_diff_empty_right_fo.p` |
| `keyset_diff_self_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_diff_self_fo.p` |
| `keyset_diff_one_hit_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_diff_one_hit_fo.p` |
| `keyset_diff_one_miss_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/keyset_diff_one_miss_fo.p` |
| `ordered_before_transitive_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/ordered_before_transitive_fo.p` |
| `has_key_keyset_singleton_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/has_key_keyset_singleton_fo.p` |
| `child_focus_child_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/child_focus_child_fo.p` |
| `child_focus_empty_absent_key_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/child_focus_empty_absent_key_fo.p` |
| `scheduler_has_key_observes_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/scheduler_has_key_observes_fo.p` |
| `scheduler_tail_frontier_observes_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/scheduler_tail_frontier_observes_fo.p` |
| `frontier_candidate_keyset_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/frontier_candidate_keyset_fo.p` |
| `frontier_state_candidate_keyset_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/frontier_state_candidate_keyset_fo.p` |
| `eager_nonempty_paths_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_nonempty_paths_set_equiv.p` |
| `eager_product_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_product_set_equiv.p` |
| `eager_restriction_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_restriction_set_equiv.p` |
| `eager_raffination_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_raffination_set_equiv.p` |
| `eager_wrap_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_wrap_set_equiv.p` |
| `eager_unwrap_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_unwrap_set_equiv.p` |
| `zipper_memo_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_memo_materialization_equiv.p` |
| `zipper_memo_terminal_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_memo_terminal_equiv.p` |
| `zipper_memo_child_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_memo_child_equiv.p` |
| `zipper_emptyz_empty_focus_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_emptyz_empty_focus_fo.p` |
| `zipper_emptyz_nonterminal_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_emptyz_nonterminal_fo.p` |
| `zipper_keyset_emptyz_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_keyset_emptyz_fo.p` |
| `zipper_keyset_trie_empty_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_keyset_trie_empty_fo.p` |
| `zipper_keyset_trie_epsilon_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_keyset_trie_epsilon_fo.p` |
| `zipper_keyset_trie_item_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_keyset_trie_item_fo.p` |
| `zipper_keyset_trie_concat_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_keyset_trie_concat_fo.p` |
| `eager_tails_union_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_tails_union_set_equiv.p` |
| `eager_tails_intersection_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_tails_intersection_set_equiv.p` |
| `eager_head_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_head_set_equiv.p` |
| `eager_prefix_closure_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_prefix_closure_set_equiv.p` |
| `eager_suffix_closure_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_suffix_closure_set_equiv.p` |
| `eager_tails_closure_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_tails_closure_set_equiv.p` |
| `eager_iteration_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_iteration_set_equiv.p` |
| `set_child_union_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_union_fo.p` |
| `set_iteration_tail_identity` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_tail_identity.p` |
| `set_iteration_head_identity` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_head_identity.p` |
| `set_iteration_reconstruct_headed` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_reconstruct_headed.p` |
| `set_iteration_prefixed_reconstruct_definition_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_prefixed_reconstruct_definition_fo.p` |
| `set_iteration_range_tail_definition_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_range_tail_definition_fo.p` |
| `set_iteration_range_reconstruct_definition_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_range_reconstruct_definition_fo.p` |
| `set_iteration_prefixed_range_reconstruct_definition_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_prefixed_range_reconstruct_definition_fo.p` |
| `set_iteration_general_body_union_distribution_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_general_body_union_distribution_fo.p` |
| `set_iteration_general_invariant_left_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_general_invariant_left_fo.p` |
| `set_iteration_general_invariant_right_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_general_invariant_right_fo.p` |
| `set_iteration_general_wrap_hoist_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_general_wrap_hoist_fo.p` |
| `set_iteration_general_product_right_hoist_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_general_product_right_hoist_fo.p` |
| `set_iteration_general_intersection_right_hoist_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_general_intersection_right_hoist_fo.p` |
| `set_iteration_general_diff_right_hoist_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_general_diff_right_hoist_fo.p` |
| `set_iteration_general_restriction_right_hoist_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_general_restriction_right_hoist_fo.p` |
| `set_iteration_general_independence_structural_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_iteration_general_independence_structural_fo.p` |
| `set_tails_intersection_closed_two_head_frontier_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_tails_intersection_closed_two_head_frontier_fo.p` |
| `set_tails_intersection_closed_frontier_refinement_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_tails_intersection_closed_frontier_refinement_fo.p` |
| `set_prefix_closure_interior_terminal_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_prefix_closure_interior_terminal_fo.p` |
| `set_product_prefix_closure_left_progress_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_product_prefix_closure_left_progress_fo.p` |
| `set_child_product_derivative` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_product_derivative.p` |
| `set_child_restriction_derivative` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_restriction_derivative.p` |
| `set_child_raffination_derivative` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_raffination_derivative.p` |
| `set_child_wrap_hit` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_wrap_hit.p` |
| `set_child_unwrap_singleton` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_unwrap_singleton.p` |
| `set_child_head` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_head.p` |
| `set_child_nonempty_paths` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_nonempty_paths.p` |
| `set_child_prefix_closure` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_prefix_closure.p` |
| `set_child_prefix_closure_below` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_prefix_closure_below.p` |
| `set_child_suffix_closure_derivative` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_suffix_closure_derivative.p` |
| `set_child_tails_closure_derivative` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_child_tails_closure_derivative.p` |
| `antimirov_suffix_frontier_state_child_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/antimirov_suffix_frontier_state_child_fo.p` |
| `antimirov_tails_frontier_state_child_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/antimirov_tails_frontier_state_child_fo.p` |
| `antimirov_suffix_frontier_nested_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/antimirov_suffix_frontier_nested_fo.p` |
| `antimirov_tails_frontier_nested_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/antimirov_tails_frontier_nested_fo.p` |
| `frontier_tail_nonempty_has_key_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/frontier_tail_nonempty_has_key_fo.p` |
| `frontier_candidate_has_key_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/frontier_candidate_has_key_fo.p` |
| `frontier_candidate_tail_frontier_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/frontier_candidate_tail_frontier_fo.p` |
| `tails_intersection_single_frontier_keyset_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/tails_intersection_single_frontier_keyset_fo.p` |
| `set_terminal_product` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_terminal_product.p` |
| `set_terminal_wrap` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_terminal_wrap.p` |
| `set_terminal_unwrap` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_terminal_unwrap.p` |
| `set_terminal_head_empty` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_terminal_head_empty.p` |
| `set_terminal_nonempty_paths_empty` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_terminal_nonempty_paths_empty.p` |
| `set_terminal_prefix_closure_empty` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_terminal_prefix_closure_empty.p` |
| `set_terminal_prefix_closure_below` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_terminal_prefix_closure_below.p` |
| `set_terminal_suffix_closure_empty` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_terminal_suffix_closure_empty.p` |
| `set_tails_closure_definition_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_tails_closure_definition_fo.p` |
| `set_range_full_sentinel` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_full_sentinel.p` |
| `set_range_empty_one_one` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_empty_one_one.p` |
| `eager_range_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/eager_range_set_equiv.p` |
| `set_range_subset_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_subset_fo.p` |
| `set_range_first_terminal_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_first_terminal_fo.p` |
| `set_range_first_child_terminal_empty_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_first_child_terminal_empty_fo.p` |
| `set_range_first_child_selected_sound_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_first_child_selected_sound_fo.p` |
| `set_range_first_child_pruned_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_first_child_pruned_fo.p` |
| `set_range_last_child_selected_sound_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_last_child_selected_sound_fo.p` |
| `set_range_last_child_pruned_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_last_child_pruned_fo.p` |
| `set_range_drop_last_child_before_last_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_drop_last_child_before_last_fo.p` |
| `set_range_drop_last_child_after_last_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/set_range_drop_last_child_after_last_fo.p` |
| `zipper_base_terminal_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_base_terminal_equiv.p` |
| `zipper_base_child_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_base_child_equiv.p` |
| `zipper_iteration_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_iteration_materialization_equiv.p` |
| `zipper_iter_tail_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_iter_tail_materialization_equiv.p` |
| `zipper_iter_head_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_iter_head_materialization_equiv.p` |
| `zipper_iter_reconstruct_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_iter_reconstruct_materialization_equiv.p` |
| `zipper_iter_prefixed_reconstruct_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_iter_prefixed_reconstruct_materialization_equiv.p` |
| `zipper_iter_range_tail_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_iter_range_tail_materialization_equiv.p` |
| `zipper_iter_range_reconstruct_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_iter_range_reconstruct_materialization_equiv.p` |
| `zipper_iter_prefixed_range_reconstruct_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_iter_prefixed_range_reconstruct_materialization_equiv.p` |
| `zipper_fixpoint_tail_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_fixpoint_tail_materialization_equiv.p` |
| `zipper_fixpoint_head_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_fixpoint_head_materialization_equiv.p` |
| `zipper_fixpoint_reconstruct_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_fixpoint_reconstruct_materialization_equiv.p` |
| `zipper_fixpoint_range_tail_full_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_fixpoint_range_tail_full_materialization_equiv.p` |
| `zipper_fixpoint_range_tail_empty_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_fixpoint_range_tail_empty_materialization_equiv.p` |
| `zipper_fixpoint_range_reconstruct_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_fixpoint_range_reconstruct_materialization_equiv.p` |
| `zipper_nonempty_paths_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_nonempty_paths_materialization_equiv.p` |
| `zipper_product_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_product_materialization_equiv.p` |
| `zipper_restriction_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_restriction_materialization_equiv.p` |
| `zipper_raffination_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_raffination_materialization_equiv.p` |
| `zipper_wrap_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_wrap_materialization_equiv.p` |
| `zipper_unwrap_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_unwrap_materialization_equiv.p` |
| `zipper_range_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_range_materialization_equiv.p` |
| `zipper_range_first_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_range_first_materialization_equiv.p` |
| `zipper_range_last_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_range_last_materialization_equiv.p` |
| `zipper_range_drop_last_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_range_drop_last_materialization_equiv.p` |
| `zipper_range_full_terminal_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_range_full_terminal_equiv.p` |
| `zipper_range_first_terminal_fo` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_range_first_terminal_fo.p` |
| `zipper_tails_union_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_tails_union_materialization_equiv.p` |
| `zipper_tails_intersection_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_tails_intersection_materialization_equiv.p` |
| `zipper_head_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_head_materialization_equiv.p` |
| `zipper_prefix_closure_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_prefix_closure_materialization_equiv.p` |
| `zipper_suffix_closure_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_suffix_closure_materialization_equiv.p` |
| `zipper_tails_closure_materialization_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_tails_closure_materialization_equiv.p` |
| `zipper_patch_child_terminal_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_patch_child_terminal_equiv.p` |
| `zipper_patch_child_hit_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_patch_child_hit_equiv.p` |
| `zipper_patch_child_miss_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_patch_child_miss_equiv.p` |
| `zipper_patch_child_identity_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_patch_child_identity_equiv.p` |
| `zipper_context_root_plug_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_root_plug_equiv.p` |
| `zipper_context_down_plug_invariance` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_down_plug_invariance.p` |
| `zipper_context_up_after_down_context` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_up_after_down_context.p` |
| `zipper_context_up_after_down_focus` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_up_after_down_focus.p` |
| `zipper_context_graft_materialization` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_graft_materialization.p` |
| `zipper_context_cursor_source_plug` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_cursor_source_plug.p` |
| `zipper_context_root_path` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_root_path.p` |
| `zipper_context_down_path` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_down_path.p` |
| `zipper_context_up_after_down_path` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_up_after_down_path.p` |
| `zipper_context_sibling_path` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_sibling_path.p` |
| `zipper_context_sibling_target_context` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_sibling_target_context.p` |
| `zipper_context_sibling_target_focus` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_sibling_target_focus.p` |
| `zipper_context_sibling_target_path` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_sibling_target_path.p` |
| `zipper_context_sibling_target_plug_invariance` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_sibling_target_plug_invariance.p` |
| `zipper_context_sibling_plug_invariance` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_context_sibling_plug_invariance.p` |
| `arbitrary_zipper_union_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_union_set_equiv.p` |
| `arbitrary_zipper_intersection_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_intersection_set_equiv.p` |
| `arbitrary_zipper_diff_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_diff_set_equiv.p` |
| `arbitrary_zipper_nonempty_paths_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_nonempty_paths_set_equiv.p` |
| `arbitrary_zipper_product_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_product_set_equiv.p` |
| `arbitrary_zipper_restriction_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_restriction_set_equiv.p` |
| `arbitrary_zipper_raffination_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_raffination_set_equiv.p` |
| `arbitrary_zipper_wrap_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_wrap_set_equiv.p` |
| `arbitrary_zipper_unwrap_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_unwrap_set_equiv.p` |
| `arbitrary_zipper_tails_union_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_tails_union_set_equiv.p` |
| `arbitrary_zipper_tails_intersection_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_tails_intersection_set_equiv.p` |
| `arbitrary_zipper_head_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_head_set_equiv.p` |
| `arbitrary_zipper_prefix_closure_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_prefix_closure_set_equiv.p` |
| `arbitrary_zipper_suffix_closure_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_suffix_closure_set_equiv.p` |
| `arbitrary_zipper_tails_closure_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_zipper_tails_closure_set_equiv.p` |
| `arbitrary_graph_union_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_graph_union_set_equiv.p` |
| `arbitrary_graph_intersection_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_graph_intersection_set_equiv.p` |
| `arbitrary_graph_diff_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_graph_diff_set_equiv.p` |
| `arbitrary_graph_iter_set_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_graph_iter_set_equiv.p` |
| `arbitrary_graph_trie_union_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_graph_trie_union_equiv.p` |
| `arbitrary_graph_zipper_union_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/arbitrary_graph_zipper_union_equiv.p` |
| `zipper_union_terminal_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_union_terminal_equiv.p` |
| `zipper_union_child_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_union_child_equiv.p` |
| `zipper_intersection_terminal_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_intersection_terminal_equiv.p` |
| `zipper_intersection_child_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_intersection_child_equiv.p` |
| `zipper_diff_terminal_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_diff_terminal_equiv.p` |
| `zipper_diff_child_equiv` | `Theorem` | `Theorem` | PASS | `proofs/vampire/generated/zipper_diff_child_equiv.p` |
| `aunt:trie_vs_reference` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/aunt_trie_vs_reference.p` |
| `aunt:space_optimized` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/aunt_space_optimized.p` |
| `aunt:zipper_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/aunt_zipper_vs_space.p` |
| `aunt:graph_execT_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/aunt_graph_execT_vs_space.p` |
| `semi-naive-datalog:trie_vs_reference` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/semi-naive-datalog_trie_vs_reference.p` |
| `semi-naive-datalog:space_optimized` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/semi-naive-datalog_space_optimized.p` |
| `semi-naive-datalog:zipper_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/semi-naive-datalog_zipper_vs_space.p` |
| `semi-naive-datalog:graph_execT_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/semi-naive-datalog_graph_execT_vs_space.p` |
| `gol:trie_vs_reference` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/gol_trie_vs_reference.p` |
| `gol:space_optimized` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/gol_space_optimized.p` |
| `gol:zipper_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/gol_zipper_vs_space.p` |
| `gol:graph_execT_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/gol_graph_execT_vs_space.p` |
| `15-puzzle:trie_vs_reference` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/15-puzzle_trie_vs_reference.p` |
| `15-puzzle:space_optimized` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/15-puzzle_space_optimized.p` |
| `15-puzzle:zipper_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/15-puzzle_zipper_vs_space.p` |
| `15-puzzle:graph_execT_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/15-puzzle_graph_execT_vs_space.p` |
| `temperature:trie_vs_reference` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/temperature_trie_vs_reference.p` |
| `temperature:space_optimized` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/temperature_space_optimized.p` |
| `temperature:zipper_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/temperature_zipper_vs_space.p` |
| `temperature:graph_execT_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/temperature_graph_execT_vs_space.p` |
| `nqueens:trie_vs_reference` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/nqueens_trie_vs_reference.p` |
| `nqueens:space_optimized` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/nqueens_space_optimized.p` |
| `nqueens:zipper_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/nqueens_zipper_vs_space.p` |
| `nqueens:graph_execT_vs_space` | `Theorem` | `Theorem` | PASS | `proofs/examples/vampire/nqueens_graph_execT_vs_space.p` |
| `fixpoint-tail-full-program:structural_backend_equivalence` | `Theorem` | `Theorem` | PASS | `proofs/open/vampire/fixpoint_tail_full_program_structural_backend_equivalence.p` |
| `aunt-full-program:structural_backend_equivalence` | `Theorem` | `Theorem` | PASS | `proofs/open/vampire/aunt_full_program_structural_backend_equivalence.p` |
| `semi-naive-datalog-full-program:structural_backend_equivalence` | `Theorem` | `Theorem` | PASS | `proofs/open/vampire/semi_naive_datalog_full_program_structural_backend_equivalence.p` |
| `gol-full-program:structural_backend_equivalence` | `Theorem` | `Theorem` | PASS | `proofs/open/vampire/gol_full_program_structural_backend_equivalence.p` |
| `temperature-full-program:structural_backend_equivalence` | `Theorem` | `Theorem` | PASS | `proofs/open/vampire/temperature_full_program_structural_backend_equivalence.p` |
| `sliding-puzzle-2x2-full-program:structural_backend_equivalence` | `Theorem` | `Theorem` | PASS | `proofs/open/vampire/sliding_puzzle_2x2_full_program_structural_backend_equivalence.p` |
| `sliding-puzzle-2x2-24-state-step-full-program:structural_backend_equivalence` | `Theorem` | `Theorem` | PASS | `proofs/open/vampire/sliding_puzzle_2x2_24_state_step_full_program_structural_backend_equivalence.p` |
| `nqueens-4-full-program:structural_backend_equivalence` | `Theorem` | `Theorem` | PASS | `proofs/open/vampire/nqueens_4_full_program_structural_backend_equivalence.p` |
| `termination:least_fixpoint_unique` | `Theorem` | `Theorem` | PASS | `terminating/least_fixpoint_unique.p` |
| `termination:bounded_growth_decrease` | `Theorem` | `Theorem` | PASS | `terminating/bounded_growth_decrease.p` |
| `termination:transitive_equiv` | `Theorem` | `Theorem` | PASS | `terminating/transitive_equiv.p` |
| `termination:datalog_a_terminates` | `Theorem` | `Theorem` | PASS | `terminating/datalog_a_terminates.p` |
| `termination:datalog_b_naive_terminates` | `Theorem` | `Theorem` | PASS | `terminating/datalog_b_naive_terminates.p` |
| `termination:datalog_b_seminaive_terminates` | `Theorem` | `Theorem` | PASS | `terminating/datalog_b_seminaive_terminates.p` |

## Z3 Law Gate

| Law | Expected | Actual | Result | Artifact |
| --- | --- | --- | --- | --- |
| `union_idempotent` | `unsat` | `unsat` | PASS | `proofs/generated/union_idempotent.smt2` |
| `union_empty_right` | `unsat` | `unsat` | PASS | `proofs/generated/union_empty_right.smt2` |
| `union_commutative` | `unsat` | `unsat` | PASS | `proofs/generated/union_commutative.smt2` |
| `union_associative` | `unsat` | `unsat` | PASS | `proofs/generated/union_associative.smt2` |
| `intersection_idempotent` | `unsat` | `unsat` | PASS | `proofs/generated/intersection_idempotent.smt2` |
| `intersection_empty_left` | `unsat` | `unsat` | PASS | `proofs/generated/intersection_empty_left.smt2` |
| `intersection_commutative` | `unsat` | `unsat` | PASS | `proofs/generated/intersection_commutative.smt2` |
| `intersection_associative` | `unsat` | `unsat` | PASS | `proofs/generated/intersection_associative.smt2` |
| `union_absorbs_intersection_subset` | `unsat` | `unsat` | PASS | `proofs/generated/union_absorbs_intersection_subset.smt2` |
| `intersection_absorbs_union_superset` | `unsat` | `unsat` | PASS | `proofs/generated/intersection_absorbs_union_superset.smt2` |
| `union_absorbs_diff_subset` | `unsat` | `unsat` | PASS | `proofs/generated/union_absorbs_diff_subset.smt2` |
| `union_difference_rejoins_removed` | `unsat` | `unsat` | PASS | `proofs/generated/union_difference_rejoins_removed.smt2` |
| `union_difference_intersection_partition` | `unsat` | `unsat` | PASS | `proofs/generated/union_difference_intersection_partition.smt2` |
| `intersection_absorbs_diff_subset` | `unsat` | `unsat` | PASS | `proofs/generated/intersection_absorbs_diff_subset.smt2` |
| `diff_empty_right` | `unsat` | `unsat` | PASS | `proofs/generated/diff_empty_right.smt2` |
| `diff_empty_left` | `unsat` | `unsat` | PASS | `proofs/generated/diff_empty_left.smt2` |
| `diff_self_empty` | `unsat` | `unsat` | PASS | `proofs/generated/diff_self_empty.smt2` |
| `diff_union_rhs` | `unsat` | `unsat` | PASS | `proofs/generated/diff_union_rhs.smt2` |
| `diff_intersection_left_subset_empty` | `unsat` | `unsat` | PASS | `proofs/generated/diff_intersection_left_subset_empty.smt2` |
| `diff_intersection_right_subset_empty` | `unsat` | `unsat` | PASS | `proofs/generated/diff_intersection_right_subset_empty.smt2` |
| `diff_union_left_cancel` | `unsat` | `unsat` | PASS | `proofs/generated/diff_union_left_cancel.smt2` |
| `diff_union_right_cancel` | `unsat` | `unsat` | PASS | `proofs/generated/diff_union_right_cancel.smt2` |
| `diff_union_minus_difference_left` | `unsat` | `unsat` | PASS | `proofs/generated/diff_union_minus_difference_left.smt2` |
| `diff_union_minus_difference_right` | `unsat` | `unsat` | PASS | `proofs/generated/diff_union_minus_difference_right.smt2` |
| `diff_nested_same_rhs` | `unsat` | `unsat` | PASS | `proofs/generated/diff_nested_same_rhs.smt2` |
| `diff_intersection_complement_left` | `unsat` | `unsat` | PASS | `proofs/generated/diff_intersection_complement_left.smt2` |
| `diff_intersection_complement_right` | `unsat` | `unsat` | PASS | `proofs/generated/diff_intersection_complement_right.smt2` |
| `diff_difference_self_left` | `unsat` | `unsat` | PASS | `proofs/generated/diff_difference_self_left.smt2` |
| `diff_difference_other_right` | `unsat` | `unsat` | PASS | `proofs/generated/diff_difference_other_right.smt2` |
| `restriction_epsilon_identity` | `unsat` | `unsat` | PASS | `proofs/generated/restriction_epsilon_identity.smt2` |
| `restriction_empty_prefixes` | `unsat` | `unsat` | PASS | `proofs/generated/restriction_empty_prefixes.smt2` |
| `union_absorbs_restriction_subset` | `unsat` | `unsat` | PASS | `proofs/generated/union_absorbs_restriction_subset.smt2` |
| `intersection_absorbs_restriction_subset` | `unsat` | `unsat` | PASS | `proofs/generated/intersection_absorbs_restriction_subset.smt2` |
| `union_absorbs_raffination_subset` | `unsat` | `unsat` | PASS | `proofs/generated/union_absorbs_raffination_subset.smt2` |
| `intersection_absorbs_raffination_subset` | `unsat` | `unsat` | PASS | `proofs/generated/intersection_absorbs_raffination_subset.smt2` |
| `restriction_union_same_source` | `unsat` | `unsat` | PASS | `proofs/generated/restriction_union_same_source.smt2` |
| `raffination_intersection_same_source` | `unsat` | `unsat` | PASS | `proofs/generated/raffination_intersection_same_source.smt2` |
| `restriction_raffination_partition` | `unsat` | `unsat` | PASS | `proofs/generated/restriction_raffination_partition.smt2` |
| `restriction_raffination_disjoint` | `unsat` | `unsat` | PASS | `proofs/generated/restriction_raffination_disjoint.smt2` |
| `diff_restriction_subset_empty` | `unsat` | `unsat` | PASS | `proofs/generated/diff_restriction_subset_empty.smt2` |
| `diff_raffination_subset_empty` | `unsat` | `unsat` | PASS | `proofs/generated/diff_raffination_subset_empty.smt2` |
| `diff_restriction_complement` | `unsat` | `unsat` | PASS | `proofs/generated/diff_restriction_complement.smt2` |
| `diff_raffination_complement` | `unsat` | `unsat` | PASS | `proofs/generated/diff_raffination_complement.smt2` |
| `wrap_unwrap_left_inverse_a` | `unsat` | `unsat` | PASS | `proofs/generated/wrap_unwrap_left_inverse_a.smt2` |
| `wrap_unwrap_left_inverse_b` | `unsat` | `unsat` | PASS | `proofs/generated/wrap_unwrap_left_inverse_b.smt2` |
| `wrap_unwrap_left_inverse_ab` | `unsat` | `unsat` | PASS | `proofs/generated/wrap_unwrap_left_inverse_ab.smt2` |
| `wrap_unwrap_restriction_a` | `unsat` | `unsat` | PASS | `proofs/generated/wrap_unwrap_restriction_a.smt2` |
| `wrap_unwrap_restriction_b` | `unsat` | `unsat` | PASS | `proofs/generated/wrap_unwrap_restriction_b.smt2` |
| `unwrap_union` | `unsat` | `unsat` | PASS | `proofs/generated/unwrap_union.smt2` |
| `product_empty_left` | `unsat` | `unsat` | PASS | `proofs/generated/product_empty_left.smt2` |
| `product_empty_right` | `unsat` | `unsat` | PASS | `proofs/generated/product_empty_right.smt2` |
| `product_epsilon_left` | `unsat` | `unsat` | PASS | `proofs/generated/product_epsilon_left.smt2` |
| `product_epsilon_right` | `unsat` | `unsat` | PASS | `proofs/generated/product_epsilon_right.smt2` |
| `child_union_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_union_a.smt2` |
| `child_union_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_union_b.smt2` |
| `child_same_head_union_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_same_head_union_a.smt2` |
| `child_same_head_union_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_same_head_union_b.smt2` |
| `child_intersection_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_intersection_a.smt2` |
| `child_intersection_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_intersection_b.smt2` |
| `child_diff_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_diff_a.smt2` |
| `child_diff_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_diff_b.smt2` |
| `child_empty_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_empty_a.smt2` |
| `child_empty_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_empty_b.smt2` |
| `child_epsilon_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_epsilon_a.smt2` |
| `child_epsilon_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_epsilon_b.smt2` |
| `child_singleton_hit_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_singleton_hit_a.smt2` |
| `child_singleton_hit_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_singleton_hit_b.smt2` |
| `child_singleton_miss_a_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_singleton_miss_a_b.smt2` |
| `child_singleton_miss_b_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_singleton_miss_b_a.smt2` |
| `child_concat_hit_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_concat_hit_a.smt2` |
| `child_concat_hit_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_concat_hit_b.smt2` |
| `child_concat_miss_a_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_concat_miss_a_b.smt2` |
| `child_concat_miss_b_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_concat_miss_b_a.smt2` |
| `child_product_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_product_a.smt2` |
| `child_product_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_product_b.smt2` |
| `child_restriction_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_restriction_a.smt2` |
| `child_restriction_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_restriction_b.smt2` |
| `tails_union_children` | `unsat` | `unsat` | PASS | `proofs/generated/tails_union_children.smt2` |
| `frontier_union_is_tails_union` | `unsat` | `unsat` | PASS | `proofs/generated/frontier_union_is_tails_union.smt2` |
| `frontier_tail_union_a_is_child` | `unsat` | `unsat` | PASS | `proofs/generated/frontier_tail_union_a_is_child.smt2` |
| `frontier_tail_union_b_is_child` | `unsat` | `unsat` | PASS | `proofs/generated/frontier_tail_union_b_is_child.smt2` |
| `frontier_child_union_a_after_b` | `unsat` | `unsat` | PASS | `proofs/generated/frontier_child_union_a_after_b.smt2` |
| `child_tails_union_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_tails_union_a.smt2` |
| `child_tails_union_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_tails_union_b.smt2` |
| `tails_intersection_two_known_heads` | `unsat` | `unsat` | PASS | `proofs/generated/tails_intersection_two_known_heads.smt2` |
| `head_idempotent` | `unsat` | `unsat` | PASS | `proofs/generated/head_idempotent.smt2` |
| `head_product` | `unsat` | `unsat` | PASS | `proofs/generated/head_product.smt2` |
| `nonempty_empty` | `unsat` | `unsat` | PASS | `proofs/generated/nonempty_empty.smt2` |
| `nonempty_epsilon_empty` | `unsat` | `unsat` | PASS | `proofs/generated/nonempty_epsilon_empty.smt2` |
| `nonempty_idempotent` | `unsat` | `unsat` | PASS | `proofs/generated/nonempty_idempotent.smt2` |
| `nonempty_subset` | `unsat` | `unsat` | PASS | `proofs/generated/nonempty_subset.smt2` |
| `nonempty_union` | `unsat` | `unsat` | PASS | `proofs/generated/nonempty_union.smt2` |
| `nonempty_child_a` | `unsat` | `unsat` | PASS | `proofs/generated/nonempty_child_a.smt2` |
| `nonempty_child_b` | `unsat` | `unsat` | PASS | `proofs/generated/nonempty_child_b.smt2` |
| `head_nonempty` | `unsat` | `unsat` | PASS | `proofs/generated/head_nonempty.smt2` |
| `patch_child_hit_a` | `unsat` | `unsat` | PASS | `proofs/generated/patch_child_hit_a.smt2` |
| `patch_child_hit_b` | `unsat` | `unsat` | PASS | `proofs/generated/patch_child_hit_b.smt2` |
| `patch_child_miss_b` | `unsat` | `unsat` | PASS | `proofs/generated/patch_child_miss_b.smt2` |
| `patch_child_miss_a` | `unsat` | `unsat` | PASS | `proofs/generated/patch_child_miss_a.smt2` |
| `patch_child_identity_a` | `unsat` | `unsat` | PASS | `proofs/generated/patch_child_identity_a.smt2` |
| `patch_child_identity_b` | `unsat` | `unsat` | PASS | `proofs/generated/patch_child_identity_b.smt2` |
| `patch_child_terminal_preserved` | `unsat` | `unsat` | PASS | `proofs/generated/patch_child_terminal_preserved.smt2` |
| `patch_child_materialization_a` | `unsat` | `unsat` | PASS | `proofs/generated/patch_child_materialization_a.smt2` |
| `iteration_tail_identity` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_tail_identity.smt2` |
| `iteration_head_identity` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_head_identity.smt2` |
| `iteration_reconstruct_nonempty_source` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_reconstruct_nonempty_source.smt2` |
| `iteration_prefixed_reconstruct_nonempty_source` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_prefixed_reconstruct_nonempty_source.smt2` |
| `iteration_prefixed_reconstruct_two_item_nonempty_source` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_prefixed_reconstruct_two_item_nonempty_source.smt2` |
| `iteration_range_tail_full_sentinel` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_tail_full_sentinel.smt2` |
| `iteration_range_reconstruct_full_sentinel` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_reconstruct_full_sentinel.smt2` |
| `iteration_prefixed_range_reconstruct_full_sentinel` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_prefixed_range_reconstruct_full_sentinel.smt2` |
| `iteration_range_tail_empty_slice` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_tail_empty_slice.smt2` |
| `iteration_range_reconstruct_empty_slice` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_reconstruct_empty_slice.smt2` |
| `iteration_prefixed_range_reconstruct_empty_slice` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_prefixed_range_reconstruct_empty_slice.smt2` |
| `iteration_range_tail_first_subset` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_tail_first_subset.smt2` |
| `iteration_range_reconstruct_first_subset` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_reconstruct_first_subset.smt2` |
| `iteration_prefixed_range_reconstruct_first_subset` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_prefixed_range_reconstruct_first_subset.smt2` |
| `iteration_range_tail_drop_last_subset` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_tail_drop_last_subset.smt2` |
| `iteration_range_reconstruct_drop_last_subset` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_reconstruct_drop_last_subset.smt2` |
| `iteration_prefixed_range_reconstruct_drop_last_subset` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_prefixed_range_reconstruct_drop_last_subset.smt2` |
| `iteration_empty_source` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_empty_source.smt2` |
| `iteration_independent_body_head_guard` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_independent_body_head_guard.smt2` |
| `iteration_source_union_tail` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_source_union_tail.smt2` |
| `iteration_source_union_head` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_source_union_head.smt2` |
| `iteration_body_union_distribution` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_body_union_distribution.smt2` |
| `iteration_source_union_reconstruct` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_source_union_reconstruct.smt2` |
| `iteration_general_wrap_hoist` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_general_wrap_hoist.smt2` |
| `iteration_general_product_right_hoist` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_general_product_right_hoist.smt2` |
| `iteration_general_intersection_right_hoist` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_general_intersection_right_hoist.smt2` |
| `iteration_general_diff_right_hoist` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_general_diff_right_hoist.smt2` |
| `iteration_general_restriction_right_hoist` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_general_restriction_right_hoist.smt2` |
| `example_puzzle_one_move_a_to_b` | `unsat` | `unsat` | PASS | `proofs/generated/example_puzzle_one_move_a_to_b.smt2` |
| `example_puzzle_one_move_b_to_a` | `unsat` | `unsat` | PASS | `proofs/generated/example_puzzle_one_move_b_to_a.smt2` |
| `iteration_range_tail_first_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_tail_first_literal.smt2` |
| `iteration_range_reconstruct_first_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_reconstruct_first_literal.smt2` |
| `iteration_prefixed_range_reconstruct_first_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_prefixed_range_reconstruct_first_literal.smt2` |
| `iteration_range_tail_drop_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_tail_drop_last_literal.smt2` |
| `iteration_range_reconstruct_drop_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_reconstruct_drop_last_literal.smt2` |
| `iteration_prefixed_range_reconstruct_drop_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_prefixed_range_reconstruct_drop_last_literal.smt2` |
| `iteration_range_tail_same_head_first_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_tail_same_head_first_literal.smt2` |
| `iteration_range_tail_same_head_drop_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_tail_same_head_drop_last_literal.smt2` |
| `iteration_range_reconstruct_same_head_first_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_reconstruct_same_head_first_literal.smt2` |
| `iteration_range_reconstruct_same_head_drop_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_range_reconstruct_same_head_drop_last_literal.smt2` |
| `iteration_prefixed_range_reconstruct_same_head_drop_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/iteration_prefixed_range_reconstruct_same_head_drop_last_literal.smt2` |
| `example_nqueens_attack_projection_2x2` | `unsat` | `unsat` | PASS | `proofs/generated/example_nqueens_attack_projection_2x2.smt2` |
| `example_nqueens_available_choice_2x2` | `unsat` | `unsat` | PASS | `proofs/generated/example_nqueens_available_choice_2x2.smt2` |
| `prefix_closure_idempotent` | `unsat` | `unsat` | PASS | `proofs/generated/prefix_closure_idempotent.smt2` |
| `suffix_closure_idempotent` | `unsat` | `unsat` | PASS | `proofs/generated/suffix_closure_idempotent.smt2` |
| `tails_closure_idempotent` | `unsat` | `unsat` | PASS | `proofs/generated/tails_closure_idempotent.smt2` |
| `suffix_closure_child_derivative_a` | `unsat` | `unsat` | PASS | `proofs/generated/suffix_closure_child_derivative_a.smt2` |
| `suffix_closure_child_derivative_b` | `unsat` | `unsat` | PASS | `proofs/generated/suffix_closure_child_derivative_b.smt2` |
| `tails_closure_definition` | `unsat` | `unsat` | PASS | `proofs/generated/tails_closure_definition.smt2` |
| `child_tails_closure_derivative_a` | `unsat` | `unsat` | PASS | `proofs/generated/child_tails_closure_derivative_a.smt2` |
| `child_tails_closure_derivative_b` | `unsat` | `unsat` | PASS | `proofs/generated/child_tails_closure_derivative_b.smt2` |
| `antimirov_suffix_frontier_state_child_a` | `unsat` | `unsat` | PASS | `proofs/generated/antimirov_suffix_frontier_state_child_a.smt2` |
| `antimirov_suffix_frontier_state_child_b` | `unsat` | `unsat` | PASS | `proofs/generated/antimirov_suffix_frontier_state_child_b.smt2` |
| `antimirov_tails_frontier_state_child_a` | `unsat` | `unsat` | PASS | `proofs/generated/antimirov_tails_frontier_state_child_a.smt2` |
| `antimirov_tails_frontier_state_child_b` | `unsat` | `unsat` | PASS | `proofs/generated/antimirov_tails_frontier_state_child_b.smt2` |
| `antimirov_suffix_frontier_nested_a_b` | `unsat` | `unsat` | PASS | `proofs/generated/antimirov_suffix_frontier_nested_a_b.smt2` |
| `antimirov_tails_frontier_nested_a_b` | `unsat` | `unsat` | PASS | `proofs/generated/antimirov_tails_frontier_nested_a_b.smt2` |
| `tails_closure_unfold_base_or_step` | `unsat` | `unsat` | PASS | `proofs/generated/tails_closure_unfold_base_or_step.smt2` |
| `fixpoint_tail_closure` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_tail_closure.smt2` |
| `fixpoint_tail_unfold_base_or_step` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_tail_unfold_base_or_step.smt2` |
| `fixpoint_tail_unfold_via_iter_tail` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_tail_unfold_via_iter_tail.smt2` |
| `fixpoint_head_closure` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_head_closure.smt2` |
| `fixpoint_head_unfold_base_or_step` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_head_unfold_base_or_step.smt2` |
| `fixpoint_reconstruct_identity` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_reconstruct_identity.smt2` |
| `fixpoint_reconstruct_unfold_base_or_step` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_reconstruct_unfold_base_or_step.smt2` |
| `fixpoint_prefixed_reconstruct_empty_prefix_identity` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_prefixed_reconstruct_empty_prefix_identity.smt2` |
| `fixpoint_range_tail_full_sentinel_closure` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_range_tail_full_sentinel_closure.smt2` |
| `fixpoint_range_tail_empty_slice_identity` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_range_tail_empty_slice_identity.smt2` |
| `fixpoint_range_reconstruct_full_sentinel_identity` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_range_reconstruct_full_sentinel_identity.smt2` |
| `fixpoint_range_reconstruct_first_identity` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_range_reconstruct_first_identity.smt2` |
| `fixpoint_range_reconstruct_drop_last_identity` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_range_reconstruct_drop_last_identity.smt2` |
| `fixpoint_prefixed_range_reconstruct_empty_prefix_first_identity` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_prefixed_range_reconstruct_empty_prefix_first_identity.smt2` |
| `fixpoint_prefixed_range_reconstruct_empty_prefix_drop_last_identity` | `unsat` | `unsat` | PASS | `proofs/generated/fixpoint_prefixed_range_reconstruct_empty_prefix_drop_last_identity.smt2` |
| `range_full_0_0` | `unsat` | `unsat` | PASS | `proofs/generated/range_full_0_0.smt2` |
| `range_empty_1_1` | `unsat` | `unsat` | PASS | `proofs/generated/range_empty_1_1.smt2` |
| `range_empty_source_first` | `unsat` | `unsat` | PASS | `proofs/generated/range_empty_source_first.smt2` |
| `range_empty_source_last` | `unsat` | `unsat` | PASS | `proofs/generated/range_empty_source_last.smt2` |
| `range_empty_source_drop_last` | `unsat` | `unsat` | PASS | `proofs/generated/range_empty_source_drop_last.smt2` |
| `range_first_wrap_a` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_wrap_a.smt2` |
| `range_last_wrap_a` | `unsat` | `unsat` | PASS | `proofs/generated/range_last_wrap_a.smt2` |
| `range_drop_last_wrap_a` | `unsat` | `unsat` | PASS | `proofs/generated/range_drop_last_wrap_a.smt2` |
| `range_first_wrap_b` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_wrap_b.smt2` |
| `range_last_wrap_b` | `unsat` | `unsat` | PASS | `proofs/generated/range_last_wrap_b.smt2` |
| `range_drop_last_wrap_b` | `unsat` | `unsat` | PASS | `proofs/generated/range_drop_last_wrap_b.smt2` |
| `range_first_wrap_ab` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_wrap_ab.smt2` |
| `range_last_wrap_ab` | `unsat` | `unsat` | PASS | `proofs/generated/range_last_wrap_ab.smt2` |
| `range_drop_last_wrap_ab` | `unsat` | `unsat` | PASS | `proofs/generated/range_drop_last_wrap_ab.smt2` |
| `range_first_subset` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_subset.smt2` |
| `range_union_absorb` | `unsat` | `unsat` | PASS | `proofs/generated/range_union_absorb.smt2` |
| `range_intersection_absorb` | `unsat` | `unsat` | PASS | `proofs/generated/range_intersection_absorb.smt2` |
| `range_first_idempotent` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_idempotent.smt2` |
| `range_last_idempotent` | `unsat` | `unsat` | PASS | `proofs/generated/range_last_idempotent.smt2` |
| `range_first_of_last` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_of_last.smt2` |
| `range_drop_last_of_first_empty` | `unsat` | `unsat` | PASS | `proofs/generated/range_drop_last_of_first_empty.smt2` |
| `range_nested_first` | `unsat` | `unsat` | PASS | `proofs/generated/range_nested_first.smt2` |
| `range_nested_suffix_first` | `unsat` | `unsat` | PASS | `proofs/generated/range_nested_suffix_first.smt2` |
| `range_nested_suffix_offset` | `unsat` | `unsat` | PASS | `proofs/generated/range_nested_suffix_offset.smt2` |
| `range_nested_last_last` | `unsat` | `unsat` | PASS | `proofs/generated/range_nested_last_last.smt2` |
| `range_positive_same_empty` | `unsat` | `unsat` | PASS | `proofs/generated/range_positive_same_empty.smt2` |
| `range_positive_decreasing_empty` | `unsat` | `unsat` | PASS | `proofs/generated/range_positive_decreasing_empty.smt2` |
| `range_negative_same_empty` | `unsat` | `unsat` | PASS | `proofs/generated/range_negative_same_empty.smt2` |
| `range_negative_decreasing_empty` | `unsat` | `unsat` | PASS | `proofs/generated/range_negative_decreasing_empty.smt2` |
| `range_last_subset` | `unsat` | `unsat` | PASS | `proofs/generated/range_last_subset.smt2` |
| `range_drop_last_subset` | `unsat` | `unsat` | PASS | `proofs/generated/range_drop_last_subset.smt2` |
| `range_negative_window_subset` | `unsat` | `unsat` | PASS | `proofs/generated/range_negative_window_subset.smt2` |
| `range_singleton_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_singleton_last_literal.smt2` |
| `range_singleton_drop_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_singleton_drop_last_literal.smt2` |
| `range_singleton_negative_window_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_singleton_negative_window_literal.smt2` |
| `range_nested_singleton_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_nested_singleton_last_literal.smt2` |
| `range_item_union_first_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_item_union_first_literal.smt2` |
| `range_item_union_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_item_union_last_literal.smt2` |
| `range_item_union_drop_last_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_item_union_drop_last_literal.smt2` |
| `range_drop_last_full_sentinel_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_drop_last_full_sentinel_literal.smt2` |
| `range_first_epsilon_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_epsilon_literal.smt2` |
| `range_first_child_border_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_child_border_literal.smt2` |
| `range_first_child_full_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_child_full_literal.smt2` |
| `range_prunes_after_upper_border_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_prunes_after_upper_border_literal.smt2` |
| `range_suffix_child_border_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_suffix_child_border_literal.smt2` |
| `range_last_border_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_last_border_literal.smt2` |
| `range_last_child_border_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_last_child_border_literal.smt2` |
| `range_last_prunes_earlier_head_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_last_prunes_earlier_head_literal.smt2` |
| `range_drop_last_border_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_drop_last_border_literal.smt2` |
| `range_drop_last_child_border_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_drop_last_child_border_literal.smt2` |
| `range_drop_last_prunes_last_head_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_drop_last_prunes_last_head_literal.smt2` |
| `range_negative_window_border_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_negative_window_border_literal.smt2` |
| `range_negative_window_child_border_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_negative_window_child_border_literal.smt2` |
| `range_negative_window_prunes_last_head_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_negative_window_prunes_last_head_literal.smt2` |
| `range_first_without_epsilon_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_without_epsilon_literal.smt2` |
| `range_first_without_epsilon_child_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_without_epsilon_child_literal.smt2` |
| `range_first_without_epsilon_prunes_later_child_literal` | `unsat` | `unsat` | PASS | `proofs/generated/range_first_without_epsilon_prunes_later_child_literal.smt2` |
| `bad_nonempty_identity_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_nonempty_identity_negative_control.smt2` |
| `bad_patch_child_identity_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_patch_child_identity_negative_control.smt2` |
| `bad_diff_commutative_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_diff_commutative_negative_control.smt2` |
| `bad_child_restriction_without_nullable_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_child_restriction_without_nullable_negative_control.smt2` |
| `bad_child_product_without_length_guard_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_child_product_without_length_guard_negative_control.smt2` |
| `bad_wrap_unwrap_wrong_prefix_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_wrap_unwrap_wrong_prefix_negative_control.smt2` |
| `bad_tails_union_as_head_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_tails_union_as_head_negative_control.smt2` |
| `bad_suffix_closure_as_prefix_closure_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_suffix_closure_as_prefix_closure_negative_control.smt2` |
| `bad_iteration_independent_without_head_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_iteration_independent_without_head_negative_control.smt2` |
| `bad_range_first_is_full_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_first_is_full_negative_control.smt2` |
| `bad_range_first_child_is_full_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_first_child_is_full_negative_control.smt2` |
| `bad_range_last_is_first_border_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_last_is_first_border_negative_control.smt2` |
| `bad_range_drop_last_keeps_last_head_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_drop_last_keeps_last_head_negative_control.smt2` |
| `bad_range_negative_window_keeps_last_head_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_negative_window_keeps_last_head_negative_control.smt2` |
| `bad_union_as_intersection_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_union_as_intersection_generated_negative_control.smt2` |
| `bad_intersection_as_union_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_intersection_as_union_generated_negative_control.smt2` |
| `bad_diff_as_intersection_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_diff_as_intersection_generated_negative_control.smt2` |
| `bad_restriction_as_raffination_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_restriction_as_raffination_generated_negative_control.smt2` |
| `bad_wrap_unwrap_wrong_prefix_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_wrap_unwrap_wrong_prefix_generated_negative_control.smt2` |
| `bad_product_commutative_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_product_commutative_generated_negative_control.smt2` |
| `bad_child_union_as_child_intersection_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_child_union_as_child_intersection_generated_negative_control.smt2` |
| `bad_tails_union_as_head_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_tails_union_as_head_generated_negative_control.smt2` |
| `bad_child_tails_union_a_drops_b_frontier_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_child_tails_union_a_drops_b_frontier_generated_negative_control.smt2` |
| `bad_child_tails_closure_a_is_child_source_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_child_tails_closure_a_is_child_source_generated_negative_control.smt2` |
| `bad_antimirov_suffix_frontier_state_is_source_child_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_antimirov_suffix_frontier_state_is_source_child_generated_negative_control.smt2` |
| `bad_antimirov_tails_frontier_state_is_source_child_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_antimirov_tails_frontier_state_is_source_child_generated_negative_control.smt2` |
| `bad_tails_intersection_as_tails_union_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_tails_intersection_as_tails_union_generated_negative_control.smt2` |
| `bad_prefix_closure_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_prefix_closure_identity_generated_negative_control.smt2` |
| `bad_suffix_closure_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_suffix_closure_identity_generated_negative_control.smt2` |
| `bad_tails_closure_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_tails_closure_identity_generated_negative_control.smt2` |
| `bad_tails_closure_without_base_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_tails_closure_without_base_generated_negative_control.smt2` |
| `bad_nonempty_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_nonempty_identity_generated_negative_control.smt2` |
| `bad_head_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_head_identity_generated_negative_control.smt2` |
| `bad_patch_child_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_patch_child_identity_generated_negative_control.smt2` |
| `bad_iteration_reconstruct_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_iteration_reconstruct_identity_generated_negative_control.smt2` |
| `bad_iteration_tail_union_as_intersection_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_iteration_tail_union_as_intersection_generated_negative_control.smt2` |
| `bad_iteration_range_tail_first_is_tail_union_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_iteration_range_tail_first_is_tail_union_generated_negative_control.smt2` |
| `bad_iteration_range_reconstruct_first_is_nonempty_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_iteration_range_reconstruct_first_is_nonempty_generated_negative_control.smt2` |
| `bad_iteration_range_tail_same_head_split_frontier_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_iteration_range_tail_same_head_split_frontier_generated_negative_control.smt2` |
| `bad_child_same_head_union_a_drops_second_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_child_same_head_union_a_drops_second_generated_negative_control.smt2` |
| `bad_child_same_head_union_b_drops_second_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_child_same_head_union_b_drops_second_generated_negative_control.smt2` |
| `bad_fixpoint_tail_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_fixpoint_tail_identity_generated_negative_control.smt2` |
| `bad_fixpoint_tail_without_base_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_fixpoint_tail_without_base_generated_negative_control.smt2` |
| `bad_fixpoint_head_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_fixpoint_head_identity_generated_negative_control.smt2` |
| `bad_fixpoint_reconstruct_as_nonempty_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_fixpoint_reconstruct_as_nonempty_generated_negative_control.smt2` |
| `bad_fixpoint_range_tail_first_as_tail_closure_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_fixpoint_range_tail_first_as_tail_closure_generated_negative_control.smt2` |
| `bad_fixpoint_prefixed_reconstruct_nonempty_prefix_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_fixpoint_prefixed_reconstruct_nonempty_prefix_identity_generated_negative_control.smt2` |
| `bad_fixpoint_prefixed_range_reconstruct_nonempty_prefix_identity_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_fixpoint_prefixed_range_reconstruct_nonempty_prefix_identity_generated_negative_control.smt2` |
| `bad_range_first_is_full_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_first_is_full_generated_negative_control.smt2` |
| `bad_range_last_is_full_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_last_is_full_generated_negative_control.smt2` |
| `bad_range_drop_last_is_full_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_drop_last_is_full_generated_negative_control.smt2` |
| `bad_range_first_distributes_over_union_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_first_distributes_over_union_generated_negative_control.smt2` |
| `bad_range_last_distributes_over_union_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_last_distributes_over_union_generated_negative_control.smt2` |
| `bad_range_wrap_first_uses_last_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_wrap_first_uses_last_generated_negative_control.smt2` |
| `bad_range_wrap_last_uses_first_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_wrap_last_uses_first_generated_negative_control.smt2` |
| `bad_range_wrap_drop_last_keeps_last_generated_negative_control` | `sat` | `sat` | PASS | `proofs/generated/bad_range_wrap_drop_last_keeps_last_generated_negative_control.smt2` |
| `aunt:trie_vs_reference` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/aunt_trie_vs_reference.smt2` |
| `aunt:space_optimized` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/aunt_space_optimized.smt2` |
| `aunt:zipper_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/aunt_zipper_vs_space.smt2` |
| `aunt:graph_execT_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/aunt_graph_execT_vs_space.smt2` |
| `semi-naive-datalog:trie_vs_reference` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/semi-naive-datalog_trie_vs_reference.smt2` |
| `semi-naive-datalog:space_optimized` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/semi-naive-datalog_space_optimized.smt2` |
| `semi-naive-datalog:zipper_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/semi-naive-datalog_zipper_vs_space.smt2` |
| `semi-naive-datalog:graph_execT_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/semi-naive-datalog_graph_execT_vs_space.smt2` |
| `gol:trie_vs_reference` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/gol_trie_vs_reference.smt2` |
| `gol:space_optimized` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/gol_space_optimized.smt2` |
| `gol:zipper_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/gol_zipper_vs_space.smt2` |
| `gol:graph_execT_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/gol_graph_execT_vs_space.smt2` |
| `15-puzzle:trie_vs_reference` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/15-puzzle_trie_vs_reference.smt2` |
| `15-puzzle:space_optimized` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/15-puzzle_space_optimized.smt2` |
| `15-puzzle:zipper_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/15-puzzle_zipper_vs_space.smt2` |
| `15-puzzle:graph_execT_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/15-puzzle_graph_execT_vs_space.smt2` |
| `temperature:trie_vs_reference` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/temperature_trie_vs_reference.smt2` |
| `temperature:space_optimized` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/temperature_space_optimized.smt2` |
| `temperature:zipper_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/temperature_zipper_vs_space.smt2` |
| `temperature:graph_execT_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/temperature_graph_execT_vs_space.smt2` |
| `nqueens:trie_vs_reference` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/nqueens_trie_vs_reference.smt2` |
| `nqueens:space_optimized` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/nqueens_space_optimized.smt2` |
| `nqueens:zipper_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/nqueens_zipper_vs_space.smt2` |
| `nqueens:graph_execT_vs_space` | `unsat` | `unsat` | PASS | `proofs/examples/smt2/nqueens_graph_execT_vs_space.smt2` |
| `union-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/union_open_space_optimized_open.smt2` |
| `union-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/union_open_raw_graph_roundtrip_open.smt2` |
| `union-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/union_open_optimized_graph_roundtrip_open.smt2` |
| `intersection-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/intersection_open_space_optimized_open.smt2` |
| `intersection-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/intersection_open_raw_graph_roundtrip_open.smt2` |
| `intersection-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/intersection_open_optimized_graph_roundtrip_open.smt2` |
| `subtraction-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/subtraction_open_space_optimized_open.smt2` |
| `subtraction-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/subtraction_open_raw_graph_roundtrip_open.smt2` |
| `subtraction-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/subtraction_open_optimized_graph_roundtrip_open.smt2` |
| `restriction-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/restriction_open_space_optimized_open.smt2` |
| `restriction-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/restriction_open_raw_graph_roundtrip_open.smt2` |
| `restriction-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/restriction_open_optimized_graph_roundtrip_open.smt2` |
| `raffination-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/raffination_open_space_optimized_open.smt2` |
| `raffination-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/raffination_open_raw_graph_roundtrip_open.smt2` |
| `raffination-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/raffination_open_optimized_graph_roundtrip_open.smt2` |
| `composition-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/composition_open_space_optimized_open.smt2` |
| `composition-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/composition_open_raw_graph_roundtrip_open.smt2` |
| `composition-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/composition_open_optimized_graph_roundtrip_open.smt2` |
| `unwrap-dynamic-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/unwrap_dynamic_open_space_optimized_open.smt2` |
| `unwrap-dynamic-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/unwrap_dynamic_open_raw_graph_roundtrip_open.smt2` |
| `unwrap-dynamic-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/unwrap_dynamic_open_optimized_graph_roundtrip_open.smt2` |
| `wrap-dynamic-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/wrap_dynamic_open_space_optimized_open.smt2` |
| `wrap-dynamic-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/wrap_dynamic_open_raw_graph_roundtrip_open.smt2` |
| `wrap-dynamic-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/wrap_dynamic_open_optimized_graph_roundtrip_open.smt2` |
| `transform-pair-swap-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/transform_pair_swap_open_space_optimized_open.smt2` |
| `transform-pair-swap-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/transform_pair_swap_open_raw_graph_roundtrip_open.smt2` |
| `transform-pair-swap-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/transform_pair_swap_open_optimized_graph_roundtrip_open.smt2` |
| `tails-union-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/tails_union_open_space_optimized_open.smt2` |
| `tails-union-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/tails_union_open_raw_graph_roundtrip_open.smt2` |
| `tails-union-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/tails_union_open_optimized_graph_roundtrip_open.smt2` |
| `tails-intersection-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/tails_intersection_open_space_optimized_open.smt2` |
| `tails-intersection-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/tails_intersection_open_raw_graph_roundtrip_open.smt2` |
| `tails-intersection-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/tails_intersection_open_optimized_graph_roundtrip_open.smt2` |
| `prefix-closure-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/prefix_closure_open_space_optimized_open.smt2` |
| `prefix-closure-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/prefix_closure_open_raw_graph_roundtrip_open.smt2` |
| `prefix-closure-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/prefix_closure_open_optimized_graph_roundtrip_open.smt2` |
| `suffix-closure-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/suffix_closure_open_space_optimized_open.smt2` |
| `suffix-closure-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/suffix_closure_open_raw_graph_roundtrip_open.smt2` |
| `suffix-closure-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/suffix_closure_open_optimized_graph_roundtrip_open.smt2` |
| `tails-closure-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/tails_closure_open_space_optimized_open.smt2` |
| `tails-closure-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/tails_closure_open_raw_graph_roundtrip_open.smt2` |
| `tails-closure-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/tails_closure_open_optimized_graph_roundtrip_open.smt2` |
| `range-first-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_first_open_space_optimized_open.smt2` |
| `range-first-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_first_open_raw_graph_roundtrip_open.smt2` |
| `range-first-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_first_open_optimized_graph_roundtrip_open.smt2` |
| `range-last-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_last_open_space_optimized_open.smt2` |
| `range-last-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_last_open_raw_graph_roundtrip_open.smt2` |
| `range-last-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_last_open_optimized_graph_roundtrip_open.smt2` |
| `range-drop-last-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_drop_last_open_space_optimized_open.smt2` |
| `range-drop-last-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_drop_last_open_raw_graph_roundtrip_open.smt2` |
| `range-drop-last-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_drop_last_open_optimized_graph_roundtrip_open.smt2` |
| `range-full-sentinel-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_full_sentinel_open_space_optimized_open.smt2` |
| `range-full-sentinel-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_full_sentinel_open_raw_graph_roundtrip_open.smt2` |
| `range-full-sentinel-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_full_sentinel_open_optimized_graph_roundtrip_open.smt2` |
| `range-negative-window-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_negative_window_open_space_optimized_open.smt2` |
| `range-negative-window-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_negative_window_open_raw_graph_roundtrip_open.smt2` |
| `range-negative-window-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/range_negative_window_open_optimized_graph_roundtrip_open.smt2` |
| `iteration-reconstruct-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_reconstruct_open_space_optimized_open.smt2` |
| `iteration-reconstruct-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_reconstruct_open_raw_graph_roundtrip_open.smt2` |
| `iteration-reconstruct-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_reconstruct_open_optimized_graph_roundtrip_open.smt2` |
| `iteration-head-tail-blend-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_head_tail_blend_open_space_optimized_open.smt2` |
| `iteration-head-tail-blend-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_head_tail_blend_open_raw_graph_roundtrip_open.smt2` |
| `iteration-head-tail-blend-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_head_tail_blend_open_optimized_graph_roundtrip_open.smt2` |
| `iteration-range-tail-first-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_range_tail_first_open_space_optimized_open.smt2` |
| `iteration-range-tail-first-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_range_tail_first_open_raw_graph_roundtrip_open.smt2` |
| `iteration-range-tail-first-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_range_tail_first_open_optimized_graph_roundtrip_open.smt2` |
| `iteration-range-reconstruct-drop-last-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_range_reconstruct_drop_last_open_space_optimized_open.smt2` |
| `iteration-range-reconstruct-drop-last-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_range_reconstruct_drop_last_open_raw_graph_roundtrip_open.smt2` |
| `iteration-range-reconstruct-drop-last-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/iteration_range_reconstruct_drop_last_open_optimized_graph_roundtrip_open.smt2` |
| `fixpoint-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/fixpoint_open_space_optimized_open.smt2` |
| `fixpoint-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/fixpoint_open_raw_graph_roundtrip_open.smt2` |
| `fixpoint-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/fixpoint_open_optimized_graph_roundtrip_open.smt2` |
| `aunt-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/aunt_open_space_optimized_open.smt2` |
| `aunt-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/aunt_open_raw_graph_roundtrip_open.smt2` |
| `aunt-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/aunt_open_optimized_graph_roundtrip_open.smt2` |
| `aunt-full-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/aunt_full_open_space_optimized_open.smt2` |
| `aunt-full-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/aunt_full_open_raw_graph_roundtrip_open.smt2` |
| `aunt-full-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/aunt_full_open_optimized_graph_roundtrip_open.smt2` |
| `semi-naive-datalog-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/semi_naive_datalog_open_space_optimized_open.smt2` |
| `semi-naive-datalog-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/semi_naive_datalog_open_raw_graph_roundtrip_open.smt2` |
| `semi-naive-datalog-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/semi_naive_datalog_open_optimized_graph_roundtrip_open.smt2` |
| `gol-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/gol_open_space_optimized_open.smt2` |
| `gol-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/gol_open_raw_graph_roundtrip_open.smt2` |
| `gol-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/gol_open_optimized_graph_roundtrip_open.smt2` |
| `gol-full-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/gol_full_open_space_optimized_open.smt2` |
| `gol-full-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/gol_full_open_raw_graph_roundtrip_open.smt2` |
| `gol-full-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/gol_full_open_optimized_graph_roundtrip_open.smt2` |
| `temperature-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/temperature_open_space_optimized_open.smt2` |
| `temperature-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/temperature_open_raw_graph_roundtrip_open.smt2` |
| `temperature-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/temperature_open_optimized_graph_roundtrip_open.smt2` |
| `sliding-puzzle-2x2-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/sliding_puzzle_2x2_open_space_optimized_open.smt2` |
| `sliding-puzzle-2x2-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/sliding_puzzle_2x2_open_raw_graph_roundtrip_open.smt2` |
| `sliding-puzzle-2x2-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/sliding_puzzle_2x2_open_optimized_graph_roundtrip_open.smt2` |
| `nqueens-4-open:space_optimized_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/nqueens_4_open_space_optimized_open.smt2` |
| `nqueens-4-open:raw_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/nqueens_4_open_raw_graph_roundtrip_open.smt2` |
| `nqueens-4-open:optimized_graph_roundtrip_open` | `unsat` | `unsat` | PASS | `proofs/open/smt2/nqueens_4_open_optimized_graph_roundtrip_open.smt2` |
| `termination:transitive_equiv_smt` | `unsat` | `unsat` | PASS | `terminating/transitive_equiv.smt2` |
| `termination:no_infinite_descent` | `unsat
unsat
unsat` | `unsat
unsat
unsat` | PASS | `terminating/no_infinite_descent.smt2` |

## Egglog Gate

| Artifact | Expected | Actual | Result |
| --- | --- | --- | --- |
| `formal.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-descend.egg` | `exit-0` | `exit-0` | PASS |
| `zipper.egg` | `exit-0` | `exit-0` | PASS |
| `terminating/intro.egg` | `exit-0` | `exit-0` | PASS |
| `terminating/total_functions.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/aunt-kg.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/context-movement.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/datalog-semi-naive.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/frontier-antimirov.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/game-of-life-small.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/iter-fixpoint.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/negative-key.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/nqueens-4.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/puzzle-2x2-step.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/range-border-child.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/range-border-operational.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/range-observation.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/tails-intersection-frontier.egg` | `exit-0` | `exit-0` | PASS |
| `zipper-egg-tests/temperature-small.egg` | `exit-0` | `exit-0` | PASS |
| `proofs/examples/egg/15-puzzle.egg` | `exit-0` | `exit-0` | PASS |
| `proofs/examples/egg/aunt.egg` | `exit-0` | `exit-0` | PASS |
| `proofs/examples/egg/gol.egg` | `exit-0` | `exit-0` | PASS |
| `proofs/examples/egg/nqueens.egg` | `exit-0` | `exit-0` | PASS |
| `proofs/examples/egg/semi-naive-datalog.egg` | `exit-0` | `exit-0` | PASS |
| `proofs/examples/egg/temperature.egg` | `exit-0` | `exit-0` | PASS |
| `proofs/generated/egg/arbitrary_backend_rewrite_equivalence.egg` | `exit-0` | `exit-0` | PASS |

## Operational Rule Manifest

- `/Users/michaelpolyntsov/.codex/worktrees/b7c6/Zippy/proofs/operational_rule_manifest.tsv` contains `582` operational rows: `149` proved-unbounded, `433` proved-bounded, `0` axiom-elsewhere, `0` UNPROVED.
- Proof debt total: `433` rows. `proved-bounded` rows are accepted by this gate but remain proof-strengthening work. No `axiom-elsewhere` operational rows remain in the current manifest. Of the proved-bounded rows, `433` are mixed FOL+bounded and `0` are bounded-only.

| Status | Tier | Rows |
| --- | --- | --- |
| `proved-bounded` | `mixed` | `433` |
| `proved-unbounded` | `FOL` | `149` |

| Family | Rows | Proved-Unbounded | Proved-Bounded | Axiom-Elsewhere | UNPROVED |
| --- | ---: | ---: | ---: | ---: | ---: |
| Iter/Fixpoint/Head | 84 | 3 | 81 | 0 | 0 |
| Range/Order | 113 | 15 | 98 | 0 | 0 |
| Closure/Frontier | 148 | 32 | 116 | 0 | 0 |
| Context/Patch | 27 | 12 | 15 | 0 | 0 |

- Highest-frequency operational symbols in the proof queue: `TrieZ` 117, `Child` 112, `EmptyZ` 71, `tail-frontier` 64, `UnionOp` 59, `WrapOp` 52, `terminal` 43, `empty-focus` 41, `nonterminal` 35, `RangeOp` 31, `RestrictionOp` 30, `iter-independent` 29.

## Limits

- Vampire proves the abstraction and local constructor equivalence obligations listed above; it does not yet prove every optimizer rewrite directly from one generated semantic table.
- The Z3 algebraic law phase is still a bounded finite-language check.
- Iteration is now in the first-order and bounded proof layers, but arbitrary higher-order template equivalence is represented by schemas plus bounded examples rather than a generated semantic table.
- Cornerstone example proofs are closed instantiated examples over their generated inputs/contexts; the open-program SMT tier covers proof-sized operator programs, benchmark skeletons, the full Aunt query over arbitrary bounded inputs, and a proof-sized full GOL helper expansion.
- DAG-shared SMT emission is used for open-program obligations; whole programs with very large literal domains are better handled by the structural FOL tier.
- The structural full-program FOL tier covers the six cornerstone examples plus a dedicated complete 24-state 2x2 sliding-puzzle step certificate. It uses constructor-specific backend equivalence lemmas and concrete literal/path definitions instead of one generic backend-denotation axiom. `Iter` now has an explicit environment-stack semantics for bound path refs and rest spaces, including nested iteration capture; `Range` now exposes membership, rank, count, normalized bounds, and half-open interval selection. `Fixpoint` now exposes the union-saturating base-or-step equation in the same structural environment, and `terminating/` adds staged least-fixpoint uniqueness plus finite-growth/descent termination evidence for representative recursion families. Full positivity/leastness obligations for arbitrary source `Fixpoint` and mutual recursion are still not discharged from one unified semantic table. `Fold` and grounded functions remain represented by shared operator semantic predicates; the next tightening step is to unfold those remaining predicates into stronger op-specific FOL lemmas.
- Operational egg `Range` no longer has the four-path fixture-shaped answer rewrites for negative-window, `RangeLast`, or `RangeDropLast`. Negative-window now decomposes to `RangeLast(RangeDropLast(src))`; `RangeLast` and `RangeDropLast` over the concrete border fixture are handled by local terminal/child movement rules instead of whole-result materialization. Broad ordered-union rewrites and generic eager `Child(Range*)` rewrites crossed the OOM-safety threshold and are intentionally not used. The focused `range-border-child.egg` artifact validates the safer ordered border-state relation (`range-child-result`) with hit, miss, absent-key, and negative probes; `range-observation.egg` now covers both the concrete four-path epsilon/a.a/a.b/b.a border fixture and a no-epsilon first-border fixture through that scheduled relation; and `range-border-operational.egg` extends the relation to concrete trie unions, virtual unions, nested drop-last, and shared-prefix/prefixed Range sources under explicit normalize/observe/range-border phases. The proof layer now adds unbounded ordered-key FOL child-border obligations for first terminal/pruning, first/last selected soundness, last pruning, and drop-last before/after pruning. The remaining tightening step is to prove full selected-branch equality for drop-last and derive the egg scheduling relations directly from the unified semantic table instead of combining those FOL obligations with bounded generated witnesses.
- The Antimirov closure-state operators now have bounded SMT artifacts for frontier union, keyed frontier tails, nested frontier child movement, and suffix/tails closure child states, plus named unbounded FOL child/nested-child bridge obligations for suffix/tails closure frontiers. Laws involving mutual recursion, leastness/positivity obligations for general Fixpoint lowering, and an unbounded bisimulation proof of the complete demand-driven frontier scheduler are not complete in this gate.
- The main proof and runtime track is intentionally path-set-only. The value-payload experiment lives under `valued/` so the unit track can fully exploit stronger set laws and remain buildable with that directory removed.
- `formal.egg` and `zipper.egg` share one Scala-generated core prelude and remain checked illustrative targets; `zipper-descend.egg` is the comprehensive operational target. Generated example egg files also come from Scala.
