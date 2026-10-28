package morkl

object ZipperEggOperatorWitness:

  private def part0(id: String): String =
    s"""; Generated operator witnesses for Head, Iter, and Range.
         |(let $$${id}_op_src (Singleton (Concat (Item "a") (Item "b"))))
         |(let $$${id}_op_zipper (TrieZ $$${id}_op_src))
         |(let $$${id}_op_virtual_range
         |  (UnionZ
         |    (PrefixZipper (Item "a") (TrieZ (Singleton (Item "b"))))
         |    (PrefixZipper (Item "b") (TrieZ (Singleton (Item "a"))))))
         |(let $$${id}_op_virtual_range_cd
         |  (UnionZ
         |    (PrefixZipper (Item "c") (TrieZ (Singleton (Item "d"))))
         |    (PrefixZipper (Item "d") (TrieZ (Singleton (Item "c"))))))
         |(let $$${id}_op_concat_virtual_terminal
         |  (Descend "b"
         |    (ConcatZ
         |      (IntersectionZ (TrieZ (Singleton (Eps))) (TrieZ (Singleton (Eps))))
         |      (TrieZ (Singleton (Item "b"))))))
         |(let $$${id}_op_concat_virtual_nonterminal_miss
         |  (Descend "b"
         |    (ConcatZ
         |      (IntersectionZ (TrieZ (Singleton (Item "a"))) (TrieZ (Singleton (Item "a"))))
         |      (TrieZ (Singleton (Item "b"))))))
         |(let $$${id}_op_frontier_memo_src
         |  (MemoZ (TrieZ (Singleton (Concat (Item "a") (Item "b"))))))
         |(let $$${id}_op_frontier_join_src
         |  (JoinAllOp3
         |    (TrieZ (Singleton (Concat (Item "a") (Item "b"))))
         |    (TrieZ (Singleton (Concat (Item "c") (Item "d"))))
         |    (EmptyZ)))
         |(let $$${id}_op_frontier_meet_src
         |  (MeetAllOp3
         |    (TrieZ (Singleton (Concat (Item "a") (Item "b"))))
         |    (TrieZ (Singleton (Concat (Item "a") (Item "b"))))
         |    (TrieZ (Singleton (Concat (Item "a") (Item "b"))))))
         |(let $$${id}_op_frontier_raffination_source
         |  (TrieZ
         |    (Union
         |      (Singleton (Concat (Item "a") (Item "b")))
         |      (Singleton (Concat (Item "c") (Item "d"))))))
         |(let $$${id}_op_frontier_raffination_prefix
         |  (TrieZ (Singleton (Item "a"))))
         |(let $$${id}_op_frontier_raffination_src
         |  (RaffinationOp
         |    $$${id}_op_frontier_raffination_source
         |    $$${id}_op_frontier_raffination_prefix))
         |(let $$${id}_op_key_union
         |  (UnionOp
         |    (TrieZ (Singleton (Item "a")))
         |    (TrieZ (Singleton (Item "c")))))
         |(let $$${id}_op_key_intersection
         |  (IntersectionOp
         |    (TrieZ (Singleton (Item "a")))
         |    (TrieZ (Singleton (Item "a")))))
         |(let $$${id}_op_key_restriction
         |  (RestrictionOp
         |    $$${id}_op_frontier_raffination_source""".stripMargin

  private def part1(id: String): String =
    s"""         |    $$${id}_op_frontier_raffination_prefix))
         |(let $$${id}_op_key_frontier_state
         |  (FrontierStateOp
         |    (FrontierTailUnionOp
         |      $$${id}_op_frontier_memo_src
         |      "a")))
         |(let $$${id}_op_key_range_first
         |  (RangeZ $$${id}_op_virtual_range "0" "1"))
         |(let $$${id}_op_key_range_last
         |  (RangeZ $$${id}_op_virtual_range "-1" "0"))
         |(let $$${id}_op_key_range_drop_last
         |  (RangeZ $$${id}_op_virtual_range "0" "-1"))
         |(let $$${id}_op_src_same_head
         |  (Union
         |    (Singleton (Concat (Item "a") (Item "b")))
         |    (Singleton (Concat (Item "a") (Item "c")))))
         |(let $$${id}_op_zipper_same_head
         |  (TrieZ $$${id}_op_src_same_head))
         |(let $$${id}_op_head_focus
         |  (Descend "a" (HeadZ $$${id}_op_zipper)))
         |(let $$${id}_op_head_nonempty_focus
         |  (Descend "a" (HeadZ (NonEmptyZ $$${id}_op_zipper))))
         |(let $$${id}_op_head_wrap_focus
         |  (Descend "tag" (HeadZ (PrefixZipper (Item "tag") $$${id}_op_zipper))))
         |(let $$${id}_op_head_wrap_miss
         |  (Descend "a" (HeadZ (PrefixZipper (Item "tag") $$${id}_op_zipper))))
       |(let $$${id}_op_iter_tail_focus
       |  (Descend "b" (IterZ $$${id}_op_zipper (TailTemplate))))
       |(let $$${id}_op_iter_head_focus
       |  (Descend "a" (IterZ $$${id}_op_zipper (HeadTemplate))))
         |(let $$${id}_op_iter_head_miss_b
         |  (Child "b" (IterZ $$${id}_op_zipper (HeadTemplate))))
         |(let $$${id}_op_iter_reconstruct_child_a
         |  (Child "a" (IterZ $$${id}_op_zipper (ReconstructTemplate))))
         |(let $$${id}_op_iter_reconstruct_focus
         |  (Descend "b" (Descend "a" (IterZ $$${id}_op_zipper (ReconstructTemplate)))))
         |(let $$${id}_op_iter_prefixed_reconstruct_child_tag
         |  (Child "tag" (IterZ $$${id}_op_zipper (PrefixedReconstructTemplate (Item "tag")))))
         |(let $$${id}_op_iter_prefixed_reconstruct_focus
         |  (Descend "b" (Descend "a" (Descend "tag" (IterZ $$${id}_op_zipper (PrefixedReconstructTemplate (Item "tag")))))))
         |(let $$${id}_op_iter_range_tail_focus
         |  (Descend "b" (IterZ $$${id}_op_zipper (RangeTailTemplate "0" "1"))))
         |(let $$${id}_op_iter_range_tail_same_head_first_keep
         |  (Descend "b" (IterZ $$${id}_op_zipper_same_head (RangeTailTemplate "0" "1"))))
         |(let $$${id}_op_grouped_child_range_first_keep
         |  (Descend "b" (RangeZ (Child "a" $$${id}_op_zipper_same_head) "0" "1")))
         |(let $$${id}_op_iter_range_tail_same_head_first_prune
         |  (Descend "c" (IterZ $$${id}_op_zipper_same_head (RangeTailTemplate "0" "1"))))
         |(let $$${id}_op_grouped_child_range_first_prune
         |  (Descend "c" (RangeZ (Child "a" $$${id}_op_zipper_same_head) "0" "1")))
         |(let $$${id}_op_iter_range_tail_same_head_drop_last_keep
         |  (Descend "b" (IterZ $$${id}_op_zipper_same_head (RangeTailTemplate "0" "-1"))))
         |(let $$${id}_op_iter_range_tail_same_head_drop_last_prune
         |  (Descend "c" (IterZ $$${id}_op_zipper_same_head (RangeTailTemplate "0" "-1"))))
           |(let $$${id}_op_iter_range_reconstruct_focus
           |  (Descend "b" (Descend "a" (IterZ $$${id}_op_zipper (RangeReconstructTemplate "0" "1")))))
           |(let $$${id}_op_iter_range_reconstruct_child_a
           |  (Child "a" (IterZ $$${id}_op_zipper (RangeReconstructTemplate "0" "1"))))
           |(let $$${id}_op_iter_range_reconstruct_same_head_first_keep
           |  (Descend "b" (Descend "a" (IterZ $$${id}_op_zipper_same_head (RangeReconstructTemplate "0" "1")))))
           |(let $$${id}_op_iter_range_reconstruct_same_head_first_prune
           |  (Descend "c" (Descend "a" (IterZ $$${id}_op_zipper_same_head (RangeReconstructTemplate "0" "1")))))
           |(let $$${id}_op_iter_range_reconstruct_same_head_drop_last_keep
           |  (Descend "b" (Descend "a" (IterZ $$${id}_op_zipper_same_head (RangeReconstructTemplate "0" "-1")))))
           |(let $$${id}_op_iter_range_reconstruct_same_head_drop_last_prune
           |  (Descend "c" (Descend "a" (IterZ $$${id}_op_zipper_same_head (RangeReconstructTemplate "0" "-1")))))
           |(let $$${id}_op_iter_prefixed_range_reconstruct_focus
           |  (Descend "b" (Descend "a" (Descend "tag" (IterZ $$${id}_op_zipper (PrefixedRangeReconstructTemplate (Item "tag") "0" "1"))))))
           |(let $$${id}_op_iter_prefixed_range_reconstruct_child_tag
           |  (Child "tag" (IterZ $$${id}_op_zipper (PrefixedRangeReconstructTemplate (Item "tag") "0" "1"))))
           |(let $$${id}_op_iter_prefixed_range_reconstruct_same_head_drop_last_keep""".stripMargin

  private def part2(id: String): String =
    s"""           |  (Descend "b" (Descend "a" (Descend "tag" (IterZ $$${id}_op_zipper_same_head (PrefixedRangeReconstructTemplate (Item "tag") "0" "-1"))))))
           |(let $$${id}_op_iter_prefixed_range_reconstruct_same_head_drop_last_prune
           |  (Descend "c" (Descend "a" (Descend "tag" (IterZ $$${id}_op_zipper_same_head (PrefixedRangeReconstructTemplate (Item "tag") "0" "-1"))))))
           |(let $$${id}_op_fixpoint_tail_focus
           |  (Descend "b" (FixpointZ $$${id}_op_zipper (TailTemplate))))
           |(let $$${id}_op_fixpoint_head_child_a
           |  (Child "a" (FixpointZ $$${id}_op_zipper (HeadTemplate))))
           |(let $$${id}_op_fixpoint_reconstruct_child_a
           |  (Child "a" (FixpointZ $$${id}_op_zipper (ReconstructTemplate))))
           |(let $$${id}_op_fixpoint_tail_unfold
           |  (FixpointZ $$${id}_op_zipper (TailTemplate)))
           |(let $$${id}_op_fixpoint_head_unfold
           |  (FixpointZ $$${id}_op_zipper (HeadTemplate)))
           |(let $$${id}_op_fixpoint_reconstruct_unfold
           |  (FixpointZ $$${id}_op_zipper (ReconstructTemplate)))
           |(let $$${id}_op_suffix_state_after_a
           |  (Child "a" (SuffixClosureOp $$${id}_op_zipper)))
           |(let $$${id}_op_range_single_focus
         |  (Descend "b" (Descend "a" (RangeZ $$${id}_op_zipper "0" "1"))))
       |(let $$${id}_op_range_nested_focus
       |  (Descend "b" (Descend "a" (RangeZ (RangeZ $$${id}_op_zipper "0" "2") "0" "1"))))
       |(let $$${id}_op_range_last_focus
         |  (Descend "b" (Descend "a" (RangeZ $$${id}_op_zipper "-1" "0"))))
         |(let $$${id}_op_range_drop_last_miss
         |  (RangeZ $$${id}_op_zipper "0" "-1"))
         |(let $$${id}_op_range_virtual_first_focus
         |  (Descend "b" (Descend "a" (RangeZ $$${id}_op_virtual_range "0" "1"))))
         |(let $$${id}_op_range_virtual_last_focus
         |  (Descend "a" (Descend "b" (RangeZ $$${id}_op_virtual_range "-1" "0"))))
         |(let $$${id}_op_range_virtual_drop_last_focus
         |  (Descend "b" (Descend "a" (RangeZ $$${id}_op_virtual_range "0" "-1"))))
         |(let $$${id}_op_range_virtual_cd_first_focus
         |  (Descend "d" (Descend "c" (RangeZ $$${id}_op_virtual_range_cd "0" "1"))))
         |(let $$${id}_op_range_virtual_cd_last_focus
         |  (Descend "c" (Descend "d" (RangeZ $$${id}_op_virtual_range_cd "-1" "0"))))
         |(let $$${id}_op_range_virtual_cd_drop_last_focus
         |  (Descend "d" (Descend "c" (RangeZ $$${id}_op_virtual_range_cd "0" "-1"))))
         |(let $$${id}_op_range_prefixed_src
         |  (PrefixZipper
         |    (Item "a")
         |    (TrieZ
         |      (Union
         |        (Singleton (Item "b"))
         |        (Singleton (Item "c"))))))
         |(let $$${id}_op_range_prefixed_first_focus
         |  (Descend "b" (Descend "a" (RangeZ $$${id}_op_range_prefixed_src "0" "1"))))
         |(let $$${id}_op_range_prefixed_last_focus
         |  (Descend "c" (Descend "a" (RangeZ $$${id}_op_range_prefixed_src "-1" "0"))))
         |(let $$${id}_op_range_prefixed_drop_last_focus
         |  (Descend "b" (Descend "a" (RangeZ $$${id}_op_range_prefixed_src "0" "-1"))))
         |(let $$${id}_op_range_virtual_first_miss
         |  (Descend "b" (RangeZ $$${id}_op_virtual_range "0" "1")))
         |(let $$${id}_op_range_virtual_drop_last_miss
         |  (Descend "b" (RangeZ $$${id}_op_virtual_range "0" "-1")))
         |(let $$${id}_op_range_virtual_cd_first_miss
         |  (Descend "d" (RangeZ $$${id}_op_virtual_range_cd "0" "1")))
         |(let $$${id}_op_range_virtual_cd_drop_last_miss
         |  (Descend "d" (RangeZ $$${id}_op_virtual_range_cd "0" "-1")))
         |(iter-child-query $$${id}_op_iter_tail_focus $$${id}_op_zipper (TailTemplate) "b")
         |(iter-child-query $$${id}_op_iter_head_focus $$${id}_op_zipper (HeadTemplate) "a")
         |(iter-child-query $$${id}_op_iter_head_miss_b $$${id}_op_zipper (HeadTemplate) "b")
         |(iter-child-query $$${id}_op_iter_reconstruct_child_a $$${id}_op_zipper (ReconstructTemplate) "a")
         |(iter-child-query $$${id}_op_iter_prefixed_reconstruct_child_tag $$${id}_op_zipper (PrefixedReconstructTemplate (Item "tag")) "tag")
         |(iter-child-query $$${id}_op_iter_range_tail_focus $$${id}_op_zipper (RangeTailTemplate "0" "1") "b")
         |(iter-child-query $$${id}_op_iter_range_reconstruct_child_a $$${id}_op_zipper (RangeReconstructTemplate "0" "1") "a")
         |(iter-child-query $$${id}_op_iter_prefixed_range_reconstruct_child_tag $$${id}_op_zipper (PrefixedRangeReconstructTemplate (Item "tag") "0" "1") "tag")
         |(fixpoint-child-query $$${id}_op_fixpoint_tail_focus $$${id}_op_zipper (TailTemplate) "b")
         |(fixpoint-child-query $$${id}_op_fixpoint_head_child_a $$${id}_op_zipper (HeadTemplate) "a")
         |(fixpoint-child-query $$${id}_op_fixpoint_reconstruct_child_a $$${id}_op_zipper (ReconstructTemplate) "a")
         |(fixpoint-unfold-query $$${id}_op_fixpoint_tail_unfold $$${id}_op_zipper (TailTemplate))
         |(fixpoint-unfold-query $$${id}_op_fixpoint_head_unfold $$${id}_op_zipper (HeadTemplate))
         |(fixpoint-unfold-query $$${id}_op_fixpoint_reconstruct_unfold $$${id}_op_zipper (ReconstructTemplate))
         |(run 256)
         |(run-schedule (saturate iter_child))
         |(run-schedule (saturate fixpoint_unfold))
         |(run 16)
         |(check (= $$${id}_op_head_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_head_nonempty_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_head_wrap_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_head_wrap_miss (EmptyZ)))
         |(check (terminal $$${id}_op_concat_virtual_terminal))
         |(check (= $$${id}_op_concat_virtual_nonterminal_miss (EmptyZ)))
         |(check
         |  (tail-frontier
         |    $$${id}_op_frontier_memo_src""".stripMargin

  private def part3(id: String): String =
    s"""         |    "a"
         |    (MemoZ (TrieZ (Singleton (Item "b"))))))
         |(check
         |  (tail-frontier
         |    $$${id}_op_frontier_join_src
         |    "c"
         |    (TrieZ (Singleton (Item "d")))))
         |(check
         |  (tail-frontier
         |    $$${id}_op_frontier_meet_src
         |    "a"
         |    (MeetAllOp3
         |      (TrieZ (Singleton (Item "b")))
         |      (TrieZ (Singleton (Item "b")))
         |      (TrieZ (Singleton (Item "b"))))))
         |(check
         |  (tail-frontier
         |    $$${id}_op_frontier_raffination_src
         |    "c"
         |    (DiffOp
         |      (TrieZ (Singleton (Item "d")))
         |      (Child "c" (RestrictionOp
         |        $$${id}_op_frontier_raffination_source
         |        $$${id}_op_frontier_raffination_prefix)))))
         |(check (has-key $$${id}_op_key_union "a"))
         |(check (has-key $$${id}_op_key_union "c"))
         |(check (has-key $$${id}_op_key_intersection "a"))
         |(fail (check (has-key $$${id}_op_key_intersection "c")))
         |(check (has-key $$${id}_op_key_restriction "a"))
         |(fail (check (has-key $$${id}_op_key_restriction "c")))
         |(check (has-key $$${id}_op_key_frontier_state "b"))
         |(fail (check (has-key $$${id}_op_key_frontier_state "a")))
         |(check (has-key $$${id}_op_key_range_first "a"))
         |(fail (check (has-key $$${id}_op_key_range_first "b")))
         |(check (has-key $$${id}_op_key_range_last "b"))
         |(fail (check (has-key $$${id}_op_key_range_last "a")))
         |(check (has-key $$${id}_op_key_range_drop_last "a"))
         |(fail (check (has-key $$${id}_op_key_range_drop_last "b")))
         |(check (nonterminal $$${id}_op_key_range_last))
         |(fail (check (= (KEmpty) (KOne "a"))))
         |(fail (check (= (KOne "a") (KOne "b"))))
         |(check (iter-child-result $$${id}_op_iter_tail_focus (FrontierChildUnionOp (FrontierUnionOp $$${id}_op_zipper) "b")))
         |(check (iter-child-result $$${id}_op_iter_head_focus (TrieZ (Singleton (Eps)))))
         |(check (iter-child-result $$${id}_op_iter_head_miss_b (EmptyZ)))
         |(check (iter-child-result $$${id}_op_iter_reconstruct_child_a (Child "a" $$${id}_op_zipper)))
         |(check (iter-child-result $$${id}_op_iter_prefixed_reconstruct_child_tag (Child "tag" (WrapOp (NonEmptyOp $$${id}_op_zipper) (Item "tag")))))
         |(check (iter-child-result $$${id}_op_iter_range_tail_focus (FrontierChildUnionOp (IterRangeTailOp $$${id}_op_zipper "0" "1") "b")))
         |(check (iter-child-result $$${id}_op_iter_range_reconstruct_child_a (FrontierChildUnionOp (IterRangeReconstructOp $$${id}_op_zipper "0" "1") "a")))
         |(check (iter-child-result $$${id}_op_iter_prefixed_range_reconstruct_child_tag (FrontierChildUnionOp (IterPrefixedRangeReconstructOp $$${id}_op_zipper (Item "tag") "0" "1") "tag")))
         |(check (fixpoint-child-result $$${id}_op_fixpoint_tail_focus (FrontierStateOp (FrontierTailUnionOp (TailsClosureOp $$${id}_op_zipper) "b"))))
         |(check (fixpoint-child-result $$${id}_op_fixpoint_head_child_a (Child "a" (UnionOp $$${id}_op_zipper (HeadOp $$${id}_op_zipper)))))
         |(check (fixpoint-child-result $$${id}_op_fixpoint_reconstruct_child_a (Child "a" $$${id}_op_zipper)))
         |(check (fixpoint-unfold-result $$${id}_op_fixpoint_tail_unfold
         |  (UnionOp $$${id}_op_zipper (IterOp (FixpointOp $$${id}_op_zipper (TailTemplate)) (TailTemplate)))))
         |(check (fixpoint-unfold-result $$${id}_op_fixpoint_head_unfold
         |  (UnionOp $$${id}_op_zipper (IterOp (FixpointOp $$${id}_op_zipper (HeadTemplate)) (HeadTemplate)))))
         |(check (fixpoint-unfold-result $$${id}_op_fixpoint_reconstruct_unfold
         |  (UnionOp $$${id}_op_zipper (IterOp (FixpointOp $$${id}_op_zipper (ReconstructTemplate)) (ReconstructTemplate)))))
         |(check (terminal $$${id}_op_iter_tail_focus))
         |(check (= $$${id}_op_iter_head_focus (TrieZ (Singleton (Eps)))))
           |(check (= $$${id}_op_iter_reconstruct_focus (TrieZ (Singleton (Eps)))))
           |(check (terminal $$${id}_op_iter_prefixed_reconstruct_focus))
           |(check (terminal $$${id}_op_iter_range_tail_focus))
           |(check (terminal $$${id}_op_grouped_child_range_first_keep))
           |(check (terminal $$${id}_op_iter_range_tail_same_head_first_keep))
           |(check (terminal $$${id}_op_iter_range_tail_same_head_drop_last_keep))
           |(check (terminal $$${id}_op_iter_range_reconstruct_focus))
           |(check (terminal $$${id}_op_iter_range_reconstruct_same_head_first_keep))
           |(check (terminal $$${id}_op_iter_range_reconstruct_same_head_drop_last_keep))
           |(check (terminal $$${id}_op_iter_prefixed_range_reconstruct_focus))
           |(check (terminal $$${id}_op_iter_prefixed_range_reconstruct_same_head_drop_last_keep))
           |(fail (check (terminal $$${id}_op_iter_range_tail_same_head_first_prune)))""".stripMargin

  private def part4(id: String): String =
    s"""           |(fail (check (terminal $$${id}_op_grouped_child_range_first_prune)))
           |(fail (check (terminal $$${id}_op_iter_range_tail_same_head_drop_last_prune)))
           |(fail (check (terminal $$${id}_op_iter_range_reconstruct_same_head_first_prune)))
           |(fail (check (terminal $$${id}_op_iter_range_reconstruct_same_head_drop_last_prune)))
           |(fail (check (terminal $$${id}_op_iter_prefixed_range_reconstruct_same_head_drop_last_prune)))
           |(check (terminal $$${id}_op_fixpoint_tail_focus))
           |(check (= $$${id}_op_suffix_state_after_a (FrontierStateOp (FrontierTailUnionOp (SuffixClosureOp $$${id}_op_zipper) "a"))))
           |(check (= $$${id}_op_range_single_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_nested_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_last_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_drop_last_miss (EmptyZ)))
         |(check (= $$${id}_op_range_virtual_first_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_virtual_last_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_virtual_drop_last_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_virtual_cd_first_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_virtual_cd_last_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_virtual_cd_drop_last_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_prefixed_first_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_prefixed_last_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_prefixed_drop_last_focus (TrieZ (Singleton (Eps)))))
         |(check (= $$${id}_op_range_virtual_first_miss (EmptyZ)))
         |(check (= $$${id}_op_range_virtual_drop_last_miss (EmptyZ)))
         |(check (= $$${id}_op_range_virtual_cd_first_miss (EmptyZ)))
         |(check (= $$${id}_op_range_virtual_cd_drop_last_miss (EmptyZ)))""".stripMargin

  def section(id: String): String =
    Vector(

      part0(id),
      part1(id),
      part2(id),
      part3(id),
      part4(id)

    ).mkString("\n")
