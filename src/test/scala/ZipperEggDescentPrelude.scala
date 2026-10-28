package morkl

object ZipperEggDescentPrelude:
  private val part0: String =
    """; Self-contained zipper implementation witness prelude.
      |;
      |; Generated example files check the operational path-membership contract for
      |; their concrete result tries.  The separate zipper-descend.egg file is the
      |; implementation-level model for recursive zipper operators.
      |
      |(datatype Path
      |  (Eps)
      |  (Item String)
      |  (Concat Path Path))
      |
      |(datatype Space
      |  (Empty)
      |  (Singleton Path)
      |  (Union Space Space))
      |
        |(datatype IterTemplate
        |  (TailTemplate)
        |  (HeadTemplate)
        |  (ReconstructTemplate)
        |  (PrefixedReconstructTemplate Path)
        |  (RangeTailTemplate String String)
        |  (RangeReconstructTemplate String String)
        |  (PrefixedRangeReconstructTemplate Path String String))
      |
      |(datatype Zipper
      |  (Descend String Zipper)
      |  (TrieZ Space)
      |  (MemoZ Zipper)
      |  (EmptyZ)
      |  (UnionZ Zipper Zipper)
      |  (JoinAllZ3 Zipper Zipper Zipper)
      |  (IntersectionZ Zipper Zipper)
      |  (MeetAllZ3 Zipper Zipper Zipper)
      |  (SubtractionZ Zipper Zipper)
      |  (RestrictionZ Zipper Zipper)
      |  (RaffinationZ Zipper Zipper)
      |  (ConcatZ Zipper Zipper)
      |  (PrefixZipper Path Zipper)
      |  (UnwrapZ Zipper Path)
      |  (NonEmptyZ Zipper)
      |  (TailsUnionZ Zipper)
      |  (TailsIntersectionZ Zipper)
      |  (PrefixClosureZ Zipper)
      |  (SuffixClosureZ Zipper)
      |  (TailsClosureZ Zipper)
      |  (RangeZ Zipper String String)
      |  (HeadZ Zipper)
      |  (IterZ Zipper IterTemplate)
      |  (FixpointZ Zipper IterTemplate)
      |  (Child String Zipper)
      |  (UnionOp Zipper Zipper)
      |  (JoinAllOp3 Zipper Zipper Zipper)
      |  (IntersectionOp Zipper Zipper)
      |  (MeetAllOp3 Zipper Zipper Zipper)
      |  (DiffOp Zipper Zipper)
      |  (RestrictionOp Zipper Zipper)
      |  (RaffinationOp Zipper Zipper)
      |  (ConcatOp Zipper Zipper)
      |  (WrapOp Zipper Path)
        |  (UnwrapOp Zipper Path)
        |  (NonEmptyOp Zipper)
        |  (TailsUnionOp Zipper)
        |  (FrontierUnionOp Zipper)
        |  (FrontierChildUnionOp Zipper String)
        |  (FrontierTailUnionOp Zipper String)
        |  (FrontierStateOp Zipper)
        |  (TailsIntersectionOp Zipper)
      |  (PrefixClosureOp Zipper)
      |  (PrefixClosureBelowOp Zipper)
      |  (SuffixClosureOp Zipper)
      |  (TailsClosureOp Zipper)
      |  (RangeOp Zipper String String)
      |  (RangeFirstOp Zipper)
      |  (RangeLastOp Zipper)
      |  (RangeDropLastOp Zipper)
        |  (HeadOp Zipper)
        |  (IterOp Zipper IterTemplate)
        |  (FixpointOp Zipper IterTemplate)
        |  (IterRangeTailOp Zipper String String)
        |  (IterRangeReconstructOp Zipper String String)
        |  (IterPrefixedRangeReconstructOp Zipper Path String String)
        |  (TerminalProductChild String Zipper Zipper))
      |
        |(datatype KeySet
        |  (KEmpty)
        |  (KOne String)
        |  (KUnion KeySet KeySet)
        |  (KIntersection KeySet KeySet)
        |  (KDiff KeySet KeySet))""".stripMargin

  private val part1: String =
    """      |
      |(rewrite (Descend item z) (Child item z))
      |(rewrite (UnionZ a b) (UnionOp a b))
      |(rewrite (JoinAllZ3 a b c) (JoinAllOp3 a b c))
      |(rewrite (IntersectionZ a b) (IntersectionOp a b))
      |(rewrite (MeetAllZ3 a b c) (MeetAllOp3 a b c))
      |(rewrite (SubtractionZ a b) (DiffOp a b))
      |(rewrite (RestrictionZ a b) (RestrictionOp a b))
      |(rewrite (RaffinationZ a b) (RaffinationOp a b))
      |(rewrite (ConcatZ a b) (ConcatOp a b))
      |(rewrite (PrefixZipper p z) (WrapOp z p))
      |(rewrite (UnwrapZ z p) (UnwrapOp z p))
      |(rewrite (NonEmptyZ z) (NonEmptyOp z))
      |(rewrite (TailsUnionZ z) (TailsUnionOp z))
      |(rewrite (TailsIntersectionZ z) (TailsIntersectionOp z))
      |(rewrite (PrefixClosureZ z) (PrefixClosureOp z))
      |(rewrite (SuffixClosureZ z) (SuffixClosureOp z))
      |(rewrite (TailsClosureZ z) (TailsClosureOp z))
      |(rewrite (RangeZ z start end) (RangeOp z start end))
      |(rewrite (HeadZ z) (HeadOp z))
        |(rewrite (IterZ z template) (IterOp z template))
        |(rewrite (FixpointZ z template) (FixpointOp z template))
        |
        |(relation terminal (Zipper))
        |(relation empty-focus (Zipper))
        |(relation nonterminal (Zipper))
        |(relation nonempty-focus (Zipper))
        |(relation has-key (Zipper String))
        |(relation observed-key (String))
        |(relation observable-focus (Zipper))
        |(relation child-focus (Zipper String Zipper))
        |(relation absent-key (Zipper String))
        |(relation keyset (Zipper KeySet))
        |(relation tail-frontier (Zipper String Zipper))
        |(relation frontier-candidate (Zipper Zipper))
        |(relation suffix-active (Zipper Zipper))
        |(relation ordered-before (String String))
        |(relation needs-first-head (Zipper))
        |(relation needs-last-head (Zipper))
        |(relation first-head (Zipper String))
        |(relation last-head (Zipper String))
        |(relation range-first-child-query (Zipper Zipper String))
        |(relation range-last-child-query (Zipper Zipper String))
        |(relation range-drop-last-child-query (Zipper Zipper String))
        |(relation range-child-result (Zipper Zipper))
        |(relation iter-child-query (Zipper Zipper IterTemplate String))
        |(relation iter-child-result (Zipper Zipper))
        |(relation fixpoint-child-query (Zipper Zipper IterTemplate String))
        |(relation fixpoint-child-result (Zipper Zipper))
        |(relation fixpoint-unfold-query (Zipper Zipper IterTemplate))
        |(relation fixpoint-unfold-result (Zipper Zipper))
        |
        |(ruleset range_border)
        |(ruleset iter_child)
        |(ruleset fixpoint_unfold)
        |
        |(rule ((ordered-before a b) (ordered-before b c))
        |      ((ordered-before a c)))
        |(ordered-before "a" "b")
        |(ordered-before "b" "c")
        |(ordered-before "c" "d")
        |(ordered-before "d" "q")
        |(ordered-before "q" "z")
        |(observed-key "a")
        |(observed-key "b")
        |(observed-key "c")
        |(observed-key "d")
        |(observed-key "q")
        |(observed-key "z")
        |
        |(rule ((needs-first-head z) (= z (TrieZ (Union a b))))
        |      ((needs-first-head (TrieZ a))
        |       (needs-first-head (TrieZ b))))
        |(rule ((needs-last-head z) (= z (TrieZ (Union a b))))
        |      ((needs-last-head (TrieZ a))
        |       (needs-last-head (TrieZ b))))
        |(rule ((needs-first-head z) (= z (UnionOp a b)))
        |      ((needs-first-head a)
        |       (needs-first-head b)))
        |(rule ((needs-last-head z) (= z (UnionOp a b)))
        |      ((needs-last-head a)
        |       (needs-last-head b)))
        |(rule ((needs-first-head z) (= z (WrapOp src (Eps))))
        |      ((needs-first-head src)))
        |(rule ((needs-last-head z) (= z (WrapOp src (Eps))))
        |      ((needs-last-head src)))
        |(rule ((needs-first-head z) (= z (TrieZ (Singleton (Item item)))))
        |      ((first-head z item)
        |       (last-head z item)))
        |(rule ((needs-last-head z) (= z (TrieZ (Singleton (Item item)))))
        |      ((last-head z item)))
        |(rule ((needs-first-head z) (= z (TrieZ (Singleton (Concat (Item item) rest)))))
        |      ((first-head z item)
        |       (last-head z item)))
        |(rule ((needs-last-head z) (= z (TrieZ (Singleton (Concat (Item item) rest)))))
        |      ((last-head z item)))
        |(rule ((needs-first-head z) (= z (TrieZ (Union a b))) (first-head (TrieZ a) left) (first-head (TrieZ b) right) (ordered-before left right))
        |      ((first-head z left)))
        |(rule ((needs-first-head z) (= z (TrieZ (Union a b))) (first-head (TrieZ a) left) (first-head (TrieZ b) right) (ordered-before right left))
        |      ((first-head z right)))
        |(rule ((needs-last-head z) (= z (TrieZ (Union a b))) (last-head (TrieZ a) left) (last-head (TrieZ b) right) (ordered-before left right))
        |      ((last-head z right)))
        |(rule ((needs-last-head z) (= z (TrieZ (Union a b))) (last-head (TrieZ a) left) (last-head (TrieZ b) right) (ordered-before right left))
        |      ((last-head z left)))
        |(rule ((needs-last-head z) (= z (TrieZ (Union a b))) (terminal (TrieZ a)) (last-head (TrieZ b) item))
        |      ((last-head z item)))
        |(rule ((needs-last-head z) (= z (TrieZ (Union a b))) (terminal (TrieZ b)) (last-head (TrieZ a) item))
        |      ((last-head z item)))
        |(rule ((needs-first-head z) (= z (UnionOp a b)) (first-head a left) (first-head b right) (ordered-before left right))
        |      ((first-head z left)))
        |(rule ((needs-first-head z) (= z (UnionOp a b)) (first-head a left) (first-head b right) (ordered-before right left))
        |      ((first-head z right)))
        |(rule ((needs-last-head z) (= z (UnionOp a b)) (last-head a left) (last-head b right) (ordered-before left right))
        |      ((last-head z right)))
        |(rule ((needs-last-head z) (= z (UnionOp a b)) (last-head a left) (last-head b right) (ordered-before right left))
        |      ((last-head z left)))
        |(rule ((needs-first-head z) (= z (WrapOp src (Eps))) (first-head src item))
        |      ((first-head z item)))
        |(rule ((needs-last-head z) (= z (WrapOp src (Eps))) (last-head src item))
        |      ((last-head z item)))
        |(rule ((needs-first-head z) (= z (WrapOp src (Item item))) (nonempty-focus src))
        |      ((first-head z item)
        |       (last-head z item)))
        |(rule ((needs-last-head z) (= z (WrapOp src (Item item))) (nonempty-focus src))
        |      ((last-head z item)))
        |(rule ((needs-first-head z) (= z (WrapOp src (Concat (Item item) rest))) (nonempty-focus src))
        |      ((first-head z item)
        |       (last-head z item)))
        |(rule ((needs-last-head z) (= z (WrapOp src (Concat (Item item) rest))) (nonempty-focus src))
        |      ((last-head z item)))
        |
        |(rule ((iter-child-query z src (TailTemplate) item))
        |      ((iter-child-result z (FrontierChildUnionOp (FrontierUnionOp src) item)))
        |      :ruleset iter_child)
        |(rule ((iter-child-query z src (HeadTemplate) item) (has-key src item))
        |      ((iter-child-result z (TrieZ (Singleton (Eps)))))
        |      :ruleset iter_child)
        |(rule ((iter-child-query z src (HeadTemplate) item) (empty-focus (Child item src)))
        |      ((iter-child-result z (EmptyZ)))
        |      :ruleset iter_child)
        |(rule ((iter-child-query z src (ReconstructTemplate) item))
        |      ((iter-child-result z (Child item src)))
        |      :ruleset iter_child)
        |(rule ((iter-child-query z src (PrefixedReconstructTemplate prefix) item))
        |      ((iter-child-result z (Child item (WrapOp (NonEmptyOp src) prefix))))
        |      :ruleset iter_child)
        |(rule ((iter-child-query z src (RangeTailTemplate start end) item))
        |      ((iter-child-result z (FrontierChildUnionOp (IterRangeTailOp src start end) item)))
        |      :ruleset iter_child)
        |(rule ((iter-child-query z src (RangeReconstructTemplate start end) item))
        |      ((iter-child-result z (FrontierChildUnionOp (IterRangeReconstructOp src start end) item)))
        |      :ruleset iter_child)
        |(rule ((iter-child-query z src (PrefixedRangeReconstructTemplate prefix start end) item))
        |      ((iter-child-result z (FrontierChildUnionOp (IterPrefixedRangeReconstructOp src prefix start end) item)))
        |      :ruleset iter_child)
        |(rule ((fixpoint-child-query z src (TailTemplate) item))
        |      ((fixpoint-child-result z (FrontierStateOp (FrontierTailUnionOp (TailsClosureOp src) item))))
        |      :ruleset iter_child)
        |(rule ((fixpoint-child-query z src (HeadTemplate) item))
        |      ((fixpoint-child-result z (Child item (UnionOp src (HeadOp src)))))
        |      :ruleset iter_child)
        |(rule ((fixpoint-child-query z src (ReconstructTemplate) item))
        |      ((fixpoint-child-result z (Child item src)))
        |      :ruleset iter_child)
        |(rule ((fixpoint-child-query z src (PrefixedReconstructTemplate (Eps)) item))
        |      ((fixpoint-child-result z (Child item src)))
        |      :ruleset iter_child)
        |(rule ((fixpoint-child-query z src (RangeTailTemplate "0" "0") item))
        |      ((fixpoint-child-result z (FrontierStateOp (FrontierTailUnionOp (TailsClosureOp src) item))))
        |      :ruleset iter_child)
        |(rule ((fixpoint-child-query z src (RangeTailTemplate "1" "1") item))
        |      ((fixpoint-child-result z (Child item src)))
        |      :ruleset iter_child)
        |(rule ((fixpoint-child-query z src (RangeReconstructTemplate start end) item))
        |      ((fixpoint-child-result z (Child item src)))
        |      :ruleset iter_child)
        |(rule ((fixpoint-child-query z src (PrefixedRangeReconstructTemplate (Eps) start end) item))
        |      ((fixpoint-child-result z (Child item src)))
        |      :ruleset iter_child)
        |
        |(rule ((fixpoint-unfold-query z src (TailTemplate)))
        |      ((fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (TailTemplate)) (TailTemplate)))))
        |      :ruleset fixpoint_unfold)
        |(rule ((fixpoint-unfold-query z src (HeadTemplate)))
        |      ((fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (HeadTemplate)) (HeadTemplate)))))
        |      :ruleset fixpoint_unfold)
        |(rule ((fixpoint-unfold-query z src (ReconstructTemplate)))
        |      ((fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (ReconstructTemplate)) (ReconstructTemplate)))))
        |      :ruleset fixpoint_unfold)
        |(rule ((fixpoint-unfold-query z src (PrefixedReconstructTemplate (Eps))))
        |      ((fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (PrefixedReconstructTemplate (Eps))) (PrefixedReconstructTemplate (Eps))))))
        |      :ruleset fixpoint_unfold)
        |(rule ((fixpoint-unfold-query z src (RangeTailTemplate "0" "0")))
        |      ((fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (RangeTailTemplate "0" "0")) (RangeTailTemplate "0" "0")))))
        |      :ruleset fixpoint_unfold)
        |(rule ((fixpoint-unfold-query z src (RangeTailTemplate "1" "1")))
        |      ((fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (RangeTailTemplate "1" "1")) (RangeTailTemplate "1" "1")))))
        |      :ruleset fixpoint_unfold)
        |(rule ((fixpoint-unfold-query z src (RangeReconstructTemplate start end)))
        |      ((fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (RangeReconstructTemplate start end)) (RangeReconstructTemplate start end)))))
        |      :ruleset fixpoint_unfold)
        |(rule ((fixpoint-unfold-query z src (PrefixedRangeReconstructTemplate (Eps) start end)))
        |      ((fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (PrefixedRangeReconstructTemplate (Eps) start end)) (PrefixedRangeReconstructTemplate (Eps) start end)))))
        |      :ruleset fixpoint_unfold)
        |
        |(rule ((= z (TrieZ (Singleton (Eps)))))
        |      ((terminal z)))
        |(rule ((= z (UnionOp a b)) (terminal a))
        |      ((terminal z)))
        |(rule ((= z (UnionOp a b)) (terminal b))
        |      ((terminal z)))
        |(rule ((= z (TrieZ (Union a b))) (terminal (TrieZ a)))
        |      ((terminal z)))
        |(rule ((= z (TrieZ (Union a b))) (terminal (TrieZ b)))
        |      ((terminal z)))
        |(rule ((= z (MemoZ a)) (terminal a))
        |      ((terminal z)))
        |(rule ((= z (JoinAllOp3 a b c)) (terminal a))
        |      ((terminal z)))
        |(rule ((= z (JoinAllOp3 a b c)) (terminal b))
        |      ((terminal z)))
        |(rule ((= z (JoinAllOp3 a b c)) (terminal c))
        |      ((terminal z)))
        |(rule ((= z (IntersectionOp a b)) (terminal a) (terminal b))
        |      ((terminal z)))
        |(rule ((= z (MeetAllOp3 a b c)) (terminal a) (terminal b) (terminal c))
        |      ((terminal z)))
        |(rule ((= z (DiffOp a b)) (terminal a) (empty-focus b))
        |      ((terminal z)))
        |(rule ((= z (DiffOp a b)) (terminal a) (nonterminal b))
        |      ((terminal z)))
        |(rule ((= z (RestrictionOp src prefixes)) (terminal src) (terminal prefixes))
        |      ((terminal z)))
        |(rule ((= z (RaffinationOp src prefixes)) (terminal (DiffOp src (RestrictionOp src prefixes))))
        |      ((terminal z)))
        |(rule ((= z (ConcatOp left right)) (terminal left) (terminal right))
        |      ((terminal z)))
        |(rule ((= z (WrapOp src (Eps))) (terminal src))
        |      ((terminal z)))
        |(rule ((= z (UnwrapOp src (Eps))) (terminal src))
        |      ((terminal z)))
        |(rule ((= z (UnwrapOp src (Item item))) (terminal (Child item src)))
        |      ((terminal z)))
        |(rule ((= z (UnwrapOp src (Concat (Item item) rest))) (terminal (UnwrapOp (Child item src) rest)))
        |      ((terminal z)))
        |(rule ((= z (TailsUnionOp src)) (tail-frontier src item tail) (terminal tail))""".stripMargin

  private val part2: String =
    """        |      ((terminal z)))
        |(rule ((= z (TailsClosureOp src)) (nonempty-focus src))
        |      ((terminal z)))
        |(rule ((= z (RangeOp src "0" "0")) (terminal src))
        |      ((terminal z)))
        |(rule ((= z (RangeFirstOp src)) (terminal src))
        |      ((terminal z)))
        |(rule ((= z (RangeDropLastOp src)) (terminal src) (has-key src item))
        |      ((terminal z)))
        |(rule ((= z (HeadOp src)))
        |      ((nonterminal z)))
        |(rule ((= z (EmptyZ)))
        |      ((empty-focus z)))
        |(rule ((= z (TrieZ (Empty))))
        |      ((empty-focus z)))
        |(rule ((= z (TrieZ (Union a b))) (empty-focus (TrieZ a)) (empty-focus (TrieZ b)))
        |      ((empty-focus z)))
        |(rule ((= z (MemoZ a)) (empty-focus a))
        |      ((empty-focus z)))
        |(rule ((= z (UnionOp a b)) (empty-focus a) (empty-focus b))
        |      ((empty-focus z)))
        |(rule ((= z (JoinAllOp3 a b c)) (empty-focus a) (empty-focus b) (empty-focus c))
        |      ((empty-focus z)))
        |(rule ((= z (IntersectionOp a b)) (empty-focus a))
        |      ((empty-focus z)))
        |(rule ((= z (IntersectionOp a b)) (empty-focus b))
        |      ((empty-focus z)))
        |(rule ((= z (MeetAllOp3 a b c)) (empty-focus a))
        |      ((empty-focus z)))
        |(rule ((= z (MeetAllOp3 a b c)) (empty-focus b))
        |      ((empty-focus z)))
        |(rule ((= z (MeetAllOp3 a b c)) (empty-focus c))
        |      ((empty-focus z)))
        |(rule ((= z (DiffOp a b)) (empty-focus a))
        |      ((empty-focus z)))
        |(rule ((= z (RestrictionOp src prefixes)) (empty-focus src))
        |      ((empty-focus z)))
        |(rule ((= z (RestrictionOp src prefixes)) (empty-focus prefixes))
        |      ((empty-focus z)))
        |(rule ((= z (RaffinationOp src prefixes)) (empty-focus (DiffOp src (RestrictionOp src prefixes))))
        |      ((empty-focus z)))
        |(rule ((= z (ConcatOp left right)) (empty-focus left))
        |      ((empty-focus z)))
        |(rule ((= z (ConcatOp left right)) (empty-focus right))
        |      ((empty-focus z)))
        |(rule ((= z (WrapOp src p)) (empty-focus src))
        |      ((empty-focus z)))
        |(rule ((= z (UnwrapOp src (Eps))) (empty-focus src))
        |      ((empty-focus z)))
        |(rule ((= z (UnwrapOp src (Item item))) (empty-focus (Child item src)))
        |      ((empty-focus z)))
        |(rule ((= z (UnwrapOp src (Concat (Item item) rest))) (empty-focus (UnwrapOp (Child item src) rest)))
        |      ((empty-focus z)))
        |(rule ((= z (NonEmptyOp (EmptyZ))))
        |      ((empty-focus z)))
        |(rule ((= z (NonEmptyOp (TrieZ (Empty)))))
        |      ((empty-focus z)))
        |(rule ((= z (NonEmptyOp (TrieZ (Singleton (Eps))))))
        |      ((empty-focus z)))
        |(rule ((= z (TailsIntersectionOp src)) (tail-frontier src item tail) (empty-focus tail))
        |      ((empty-focus z)))
        |(rule ((= z (PrefixClosureBelowOp src)) (empty-focus src))
        |      ((empty-focus z)))
        |(rule ((= z (RangeOp src "1" "1")))
        |      ((empty-focus z)))
        |(rule ((= z (RangeFirstOp src)) (empty-focus src))
        |      ((empty-focus z)))
        |(rule ((= z (RangeLastOp src)) (empty-focus src))
        |      ((empty-focus z)))
        |(rule ((= z (RangeDropLastOp src)) (empty-focus src))
        |      ((empty-focus z)))
        |(rule ((= z (HeadOp src)) (empty-focus src))
        |      ((empty-focus z)))
        |(rule ((= z (EmptyZ)))
        |      ((nonterminal z)))
        |(rule ((= z (TrieZ (Empty))))
        |      ((nonterminal z)))
        |(rule ((= z (TrieZ (Singleton (Item head)))))
        |      ((nonterminal z)))
        |(rule ((= z (TrieZ (Singleton (Concat (Item head) rest)))))
        |      ((nonterminal z)))
        |(rule ((= z (TrieZ (Union a b))) (nonterminal (TrieZ a)) (nonterminal (TrieZ b)))
        |      ((nonterminal z)))
        |(rule ((= z (MemoZ src)) (nonterminal src))
        |      ((nonterminal z)))
        |(rule ((= z (UnionOp a b)) (nonterminal a) (nonterminal b))
        |      ((nonterminal z)))
        |(rule ((= z (JoinAllOp3 a b c)) (nonterminal a) (nonterminal b) (nonterminal c))
        |      ((nonterminal z)))
        |(rule ((= z (IntersectionOp a b)) (nonterminal a))
        |      ((nonterminal z)))
        |(rule ((= z (IntersectionOp a b)) (nonterminal b))""".stripMargin

  private val part3: String =
    """        |      ((nonterminal z)))
        |(rule ((= z (MeetAllOp3 a b c)) (nonterminal a))
        |      ((nonterminal z)))
        |(rule ((= z (MeetAllOp3 a b c)) (nonterminal b))
        |      ((nonterminal z)))
        |(rule ((= z (MeetAllOp3 a b c)) (nonterminal c))
        |      ((nonterminal z)))
        |(rule ((= z (DiffOp a b)) (nonterminal a))
        |      ((nonterminal z)))
        |(rule ((= z (DiffOp a b)) (terminal b))
        |      ((nonterminal z)))
        |(rule ((= z (RestrictionOp src prefixes)) (nonterminal src))
        |      ((nonterminal z)))
        |(rule ((= z (RestrictionOp src prefixes)) (nonterminal prefixes))
        |      ((nonterminal z)))
        |(rule ((= z (RaffinationOp src prefixes)) (nonterminal (DiffOp src (RestrictionOp src prefixes))))
        |      ((nonterminal z)))
        |(rule ((= z (ConcatOp left right)) (nonterminal left))
        |      ((nonterminal z)))
        |(rule ((= z (ConcatOp left right)) (nonterminal right))
        |      ((nonterminal z)))
        |(rule ((= z (WrapOp src (Eps))) (nonterminal src))
        |      ((nonterminal z)))
        |(rule ((= z (WrapOp src (Item head))))
        |      ((nonterminal z)))
        |(rule ((= z (WrapOp src (Concat (Item head) rest))))
        |      ((nonterminal z)))
        |(rule ((= z (UnwrapOp src (Eps))) (nonterminal src))
        |      ((nonterminal z)))
        |(rule ((= z (NonEmptyOp src)))
        |      ((nonterminal z)))
        |(rule ((= z (RangeOp src "1" "1")))
        |      ((nonterminal z)))
        |(rule ((= z (RangeFirstOp src)) (nonterminal src))
        |      ((nonterminal z)))
        |(rule ((= z (RangeLastOp src)) (has-key src item))
        |      ((nonterminal z)))
        |(rule ((terminal z))
        |      ((nonempty-focus z)))
        |(rule ((= z (TrieZ (Singleton (Item head)))))
        |      ((nonempty-focus z)))
        |(rule ((= z (TrieZ (Singleton (Concat (Item head) rest)))))
        |      ((nonempty-focus z)))
        |(rule ((= z (TrieZ (Union a b))) (nonempty-focus (TrieZ a)))
        |      ((nonempty-focus z)))
        |(rule ((= z (TrieZ (Union a b))) (nonempty-focus (TrieZ b)))
        |      ((nonempty-focus z)))
        |(rule ((= z (MemoZ src)) (nonempty-focus src))
        |      ((nonempty-focus z)))
        |(rule ((= z (UnionOp a b)) (nonempty-focus a))
        |      ((nonempty-focus z)))
        |(rule ((= z (UnionOp a b)) (nonempty-focus b))
        |      ((nonempty-focus z)))
        |(rule ((= z (JoinAllOp3 a b c)) (nonempty-focus a))
        |      ((nonempty-focus z)))
        |(rule ((= z (JoinAllOp3 a b c)) (nonempty-focus b))
        |      ((nonempty-focus z)))
        |(rule ((= z (JoinAllOp3 a b c)) (nonempty-focus c))
        |      ((nonempty-focus z)))
        |(rule ((terminal (Child item z)))
        |      ((has-key z item)))
        |(rule ((has-key (Child item z) child))
        |      ((has-key z item)))
        |(rule ((tail-frontier z item tail) (nonempty-focus tail))
        |      ((has-key z item)))
        |(rule ((observed-key item) (observable-focus z))
        |      ((child-focus z item (Child item z))))
        |(rule ((child-focus z item child) (empty-focus child))
        |      ((absent-key z item)))
        |(rule ((has-key z item))
        |      ((nonempty-focus z)
        |       (observed-key item)))
        |(rule ((has-key z item))
        |      ((keyset z (KOne item))))
        |(rule ((= src (TrieZ (Singleton (Item item)))))
        |      ((tail-frontier src item (TrieZ (Singleton (Eps))))))
        |(rule ((= src (TrieZ (Singleton (Concat (Item item) rest)))))
        |      ((tail-frontier src item (TrieZ (Singleton rest)))))
        |(rule ((= src (TrieZ (Union
        |                       (Singleton (Concat (Item item) left-rest))
        |                       (Singleton (Concat (Item item) right-rest))))))
        |      ((tail-frontier src item (TrieZ (Singleton left-rest)))
        |       (tail-frontier src item (TrieZ (Singleton right-rest)))))
        |(rule ((= src (TrieZ (Union
        |                       (Singleton (Concat (Item item) first-rest))
        |                       (Union
        |                         (Singleton (Concat (Item item) second-rest))
        |                         (Singleton (Concat (Item item) third-rest)))))))
        |      ((tail-frontier src item (TrieZ (Singleton first-rest)))
        |       (tail-frontier src item (TrieZ (Singleton second-rest)))
        |       (tail-frontier src item (TrieZ (Singleton third-rest)))))
        |(rule ((= src (TrieZ (Union
        |                       (Union
        |                         (Singleton (Concat (Item item) first-rest))
        |                         (Singleton (Concat (Item item) second-rest)))
        |                       (Singleton (Concat (Item item) third-rest))))))
        |      ((tail-frontier src item (TrieZ (Singleton first-rest)))
        |       (tail-frontier src item (TrieZ (Singleton second-rest)))
        |       (tail-frontier src item (TrieZ (Singleton third-rest)))))
        |(rule ((= src (TrieZ (Union a b))) (tail-frontier (TrieZ a) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (TrieZ (Union a b))) (tail-frontier (TrieZ b) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (TrieZ (Union (Union a b) c))) (tail-frontier (TrieZ a) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (TrieZ (Union (Union a b) c))) (tail-frontier (TrieZ b) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (TrieZ (Union (Union a b) c))) (tail-frontier (TrieZ c) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (TrieZ (Union a (Union b c)))) (tail-frontier (TrieZ a) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (TrieZ (Union a (Union b c)))) (tail-frontier (TrieZ b) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (TrieZ (Union a (Union b c)))) (tail-frontier (TrieZ c) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (MemoZ z)) (tail-frontier z item tail))
        |      ((tail-frontier src item (MemoZ tail))))
        |(rule ((= src (UnionOp a b)) (tail-frontier a item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (UnionOp a b)) (tail-frontier b item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (JoinAllOp3 a b c)) (tail-frontier a item tail))
        |      ((tail-frontier src item tail)))""".stripMargin

  private val part4: String =
    """        |(rule ((= src (JoinAllOp3 a b c)) (tail-frontier b item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (JoinAllOp3 a b c)) (tail-frontier c item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (IntersectionOp a b)) (tail-frontier a item left-tail) (tail-frontier b item right-tail))
        |      ((tail-frontier src item (IntersectionOp left-tail right-tail))))
        |(rule ((= src (MeetAllOp3 a b c)) (tail-frontier a item tail-a) (tail-frontier b item tail-b) (tail-frontier c item tail-c))
        |      ((tail-frontier src item (MeetAllOp3 tail-a tail-b tail-c))))
        |(rule ((= src (DiffOp a b)) (tail-frontier a item tail))
        |      ((tail-frontier src item (DiffOp tail (Child item b)))))
        |(rule ((= src (RestrictionOp source prefixes)) (terminal prefixes) (tail-frontier source item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (RestrictionOp source prefixes)) (nonterminal prefixes) (tail-frontier source item source-tail) (tail-frontier prefixes item prefix-tail))
        |      ((tail-frontier src item (RestrictionOp source-tail prefix-tail))))
        |(rule ((= src (RaffinationOp source prefixes)) (tail-frontier source item source-tail))
        |      ((tail-frontier src item (DiffOp source-tail (Child item (RestrictionOp source prefixes))))))
        |(rule ((= src (RaffinationOp source prefixes)) (tail-frontier (DiffOp source (RestrictionOp source prefixes)) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (ConcatOp left right)) (tail-frontier left item left-tail))
        |      ((tail-frontier src item (ConcatOp left-tail right))))
        |(rule ((= src (ConcatOp left right)) (terminal left) (tail-frontier right item right-tail))
        |      ((tail-frontier src item right-tail)))
        |(rule ((= src (WrapOp z (Eps))) (tail-frontier z item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (WrapOp z (Item item))))
        |      ((tail-frontier src item z)))
        |(rule ((= src (WrapOp z (Concat (Item item) rest))))
        |      ((tail-frontier src item (WrapOp z rest))))
        |(rule ((= src (UnwrapOp z (Eps))) (tail-frontier z item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (UnwrapOp z (Item head))) (tail-frontier (Child head z) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (UnwrapOp z (Concat (Item head) rest))) (tail-frontier (UnwrapOp (Child head z) rest) item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (NonEmptyOp z)) (tail-frontier z item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (RangeOp z "0" "0")) (tail-frontier z item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (HeadOp z)) (has-key z item))
        |      ((tail-frontier src item (TrieZ (Singleton (Eps))))))
        |(rule ((tail-frontier src item tail))
        |      ((observed-key item)
        |       (observable-focus tail)))
        |(rule ((= z (Child item (RangeFirstOp src))))
        |      ((needs-first-head src)
        |       (range-first-child-query z src item))
        |      :ruleset range_border)
        |(rule ((= z (Child item (RangeLastOp src))))
        |      ((needs-last-head src)
        |       (range-last-child-query z src item))
        |      :ruleset range_border)
        |(rule ((= z (Child item (RangeDropLastOp src))))
        |      ((needs-last-head src)
        |       (range-drop-last-child-query z src item))
        |      :ruleset range_border)
        |(rule ((range-first-child-query z src item) (terminal src))
        |      ((range-child-result z (EmptyZ)))
        |      :ruleset range_border)
        |(rule ((range-first-child-query z src item) (first-head src item))
        |      ((range-child-result z (RangeFirstOp (Child item src))))
        |      :ruleset range_border)
        |(rule ((range-first-child-query z src item) (first-head src first) (!= item first))
        |      ((range-child-result z (EmptyZ)))
        |      :ruleset range_border)
        |(rule ((range-last-child-query z src item) (last-head src item))
        |      ((range-child-result z (RangeLastOp (Child item src))))
        |      :ruleset range_border)
        |(rule ((range-last-child-query z src item) (last-head src last) (!= item last))
        |      ((range-child-result z (EmptyZ)))
        |      :ruleset range_border)
        |(rule ((range-drop-last-child-query z src item) (last-head src item))
        |      ((range-child-result z (RangeDropLastOp (Child item src))))
        |      :ruleset range_border)
        |(rule ((range-drop-last-child-query z src item) (last-head src last) (ordered-before item last))
        |      ((range-child-result z (Child item src)))
        |      :ruleset range_border)
        |(rule ((range-drop-last-child-query z src item) (last-head src last) (ordered-before last item))
        |      ((range-child-result z (EmptyZ)))
        |      :ruleset range_border)
        |(rule ((range-first-child-query z src item) (range-child-result z result))
        |      ((tail-frontier (RangeFirstOp src) item result))
        |      :ruleset range_border)
        |(rule ((range-last-child-query z src item) (range-child-result z result))
        |      ((tail-frontier (RangeLastOp src) item result))
        |      :ruleset range_border)
        |(rule ((range-drop-last-child-query z src item) (range-child-result z result))
        |      ((tail-frontier (RangeDropLastOp src) item result))
        |      :ruleset range_border)
        |(rule ((= z (FrontierUnionOp src)) (tail-frontier src head tail))
        |      ((frontier-candidate z tail)))
          |(rule ((= z (FrontierTailUnionOp src item)) (tail-frontier src item tail))
          |      ((frontier-candidate z tail)))
          |(rule ((= z (FrontierChildUnionOp src item)) (frontier-candidate src candidate))
          |      ((frontier-candidate z (Child item candidate))))
          |(rule ((= z (FrontierStateOp active)) (frontier-candidate active candidate))
          |      ((frontier-candidate z candidate)))
          |(rule ((= z (FrontierStateOp active)) (frontier-candidate active candidate) (terminal candidate))
          |      ((terminal z)))
          |(rule ((= z (FrontierStateOp active)) (frontier-candidate active candidate) (has-key candidate item))
          |      ((has-key z item)))
          |(rule ((= z (FrontierStateOp active)) (frontier-candidate active candidate) (keyset candidate ks))
          |      ((keyset z ks)))
          |(rule ((= z (FrontierStateOp active)) (frontier-candidate active candidate) (tail-frontier candidate item tail))
          |      ((tail-frontier z item tail)))
          |(rule ((= z (Child item (FrontierStateOp active))) (frontier-candidate active candidate) (terminal (Child item candidate)))
          |      ((terminal z)))
          |(rule ((= z (Child item (FrontierStateOp active))) (frontier-candidate active candidate) (has-key (Child item candidate) child))
          |      ((has-key z child)))
          |(rule ((= z (Child next (FrontierStateOp (FrontierTailUnionOp src item)))) (tail-frontier src item tail) (terminal (Child next tail)))
          |      ((terminal z)))
          |(rule ((= z (Child next (FrontierStateOp (FrontierTailUnionOp src item)))) (tail-frontier src item tail) (has-key (Child next tail) child))
          |      ((has-key z child)))
          |(rule ((= z (IterRangeTailOp src start end)) (tail-frontier src head tail))
          |      ((frontier-candidate z (RangeOp (Child head src) start end))))
          |(rule ((= z (IterRangeReconstructOp src start end)) (tail-frontier src head tail))
          |      ((frontier-candidate z (WrapOp (RangeOp (Child head src) start end) (Item head)))))
          |(rule ((= z (IterPrefixedRangeReconstructOp src prefix start end)) (tail-frontier src head tail))
          |      ((frontier-candidate z (WrapOp (RangeOp (Child head src) start end) (Concat prefix (Item head))))))
          |(rule ((frontier-candidate src candidate) (tail-frontier candidate item tail))
          |      ((tail-frontier src item tail)))
        |(rule ((frontier-candidate z candidate) (terminal candidate))
        |      ((terminal z)))
        |(rule ((frontier-candidate z candidate) (has-key candidate item))
        |      ((has-key z item)))
        |(rule ((frontier-candidate z candidate) (keyset candidate ks))
        |      ((keyset z ks)))
        |(rule ((= closure (SuffixClosureOp root)))
        |      ((suffix-active root root)))
        |(rule ((= closure (TailsClosureOp root)))
        |      ((suffix-active root root)))
        |(rule ((suffix-active root active) (tail-frontier active head tail))
        |      ((suffix-active root tail)))
        |(rule ((= src (SuffixClosureOp root)) (suffix-active root active) (tail-frontier active item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (TailsClosureOp root)) (suffix-active root active) (tail-frontier active item tail))
        |      ((tail-frontier src item tail)))
        |(rule ((= src (SuffixClosureOp root)) (tail-frontier src item tail) (nonempty-focus tail))
        |      ((has-key src item)))
        |(rule ((= src (TailsClosureOp root)) (tail-frontier src item tail) (nonempty-focus tail))
        |      ((has-key src item)))
        |""".stripMargin

  private val part5: String =
    """        |(rewrite (KUnion (KEmpty) keys) keys)
        |(rewrite (KUnion keys (KEmpty)) keys)
        |(rewrite (KUnion keys keys) keys)
        |(rewrite (KIntersection (KEmpty) keys) (KEmpty))
        |(rewrite (KIntersection keys (KEmpty)) (KEmpty))
        |(rewrite (KIntersection keys keys) keys)
        |(rewrite (KIntersection (KOne item) (KOne item)) (KOne item))
        |(rewrite (KIntersection (KOne item) (KOne other)) (KEmpty) :when ((!= item other)))
        |(rewrite (KDiff (KEmpty) keys) (KEmpty))
        |(rewrite (KDiff keys (KEmpty)) keys)
        |(rewrite (KDiff keys keys) (KEmpty))
        |(rewrite (KDiff (KOne item) (KOne item)) (KEmpty))
        |(rewrite (KDiff (KOne item) (KOne other)) (KOne item) :when ((!= item other)))
        |(rule ((= z (EmptyZ)))
        |      ((keyset z (KEmpty))))
        |(rule ((= z (TrieZ (Empty))))
        |      ((keyset z (KEmpty))))
        |(rule ((= z (TrieZ (Singleton (Eps)))))
        |      ((keyset z (KEmpty))))
        |(rule ((= z (TrieZ (Singleton (Item head)))))
        |      ((keyset z (KOne head))))
        |(rule ((= z (TrieZ (Singleton (Concat (Item head) rest)))))
        |      ((keyset z (KOne head))))
        |; Composite schedule information is checked through has-key/tail-frontier.
        |; Keeping keyset facts concrete avoids constructing infinitely many equivalent
        |; KUnion/KIntersection/KDiff witnesses for recursive virtual DAGs.
        |
        |(rewrite (TrieZ (Empty)) (EmptyZ))
      |(rewrite (UnionOp (EmptyZ) z) z)
      |(rewrite (UnionOp z (EmptyZ)) z)
      |(rewrite (JoinAllOp3 (EmptyZ) (EmptyZ) z) z)
      |(rewrite (JoinAllOp3 (EmptyZ) z (EmptyZ)) z)
      |(rewrite (JoinAllOp3 z (EmptyZ) (EmptyZ)) z)
      |(rewrite (JoinAllOp3 (EmptyZ) a b) (UnionOp a b))
      |(rewrite (JoinAllOp3 a (EmptyZ) b) (UnionOp a b))
      |(rewrite (JoinAllOp3 a b (EmptyZ)) (UnionOp a b))
      |(rewrite (IntersectionOp (EmptyZ) z) (EmptyZ))
      |(rewrite (IntersectionOp z (EmptyZ)) (EmptyZ))
      |(rewrite (MeetAllOp3 (EmptyZ) a b) (EmptyZ))
      |(rewrite (MeetAllOp3 a (EmptyZ) b) (EmptyZ))
      |(rewrite (MeetAllOp3 a b (EmptyZ)) (EmptyZ))
      |(rewrite (DiffOp (EmptyZ) z) (EmptyZ))
      |(rewrite (DiffOp z (EmptyZ)) z)
      |(rewrite (RestrictionOp (EmptyZ) z) (EmptyZ))
      |(rewrite (RestrictionOp z (EmptyZ)) (EmptyZ))
      |(rewrite (RestrictionOp z (TrieZ (Singleton (Eps)))) z)
      |(rewrite (RestrictionOp z (UnionOp (TrieZ (Singleton (Eps))) prefixes)) z)
      |(rewrite (RestrictionOp z (UnionOp prefixes (TrieZ (Singleton (Eps))))) z)
      |(rewrite (RaffinationOp z prefixes) (DiffOp z (RestrictionOp z prefixes)))
      |(rewrite (ConcatOp (EmptyZ) z) (EmptyZ))
      |(rewrite (ConcatOp z (EmptyZ)) (EmptyZ))
      |(rewrite (WrapOp (EmptyZ) p) (EmptyZ))
      |(rewrite (WrapOp z (Eps)) z)
      |(rewrite (UnwrapOp (EmptyZ) p) (EmptyZ))
      |(rewrite (UnwrapOp z (Eps)) z)
      |(rewrite (NonEmptyOp (EmptyZ)) (EmptyZ))
      |(rewrite (NonEmptyOp (TrieZ (Singleton (Eps)))) (EmptyZ))
      |(rewrite (TailsUnionOp (EmptyZ)) (EmptyZ))
      |(rewrite (TailsIntersectionOp (EmptyZ)) (EmptyZ))
      |(rewrite (PrefixClosureOp (EmptyZ)) (EmptyZ))
      |(rewrite (SuffixClosureOp (EmptyZ)) (EmptyZ))
      |(rewrite (TailsClosureOp (EmptyZ)) (EmptyZ))
      |(rewrite (RangeOp (EmptyZ) start end) (EmptyZ))
      |(rewrite (RangeOp z "0" "0") z)
      |(rewrite (RangeOp z "1" "1") (EmptyZ))
      |(rewrite (RangeOp z "0" "1") (RangeFirstOp z))
      |(rewrite (RangeOp z "-1" "0") (RangeLastOp z))
      |(rewrite (RangeOp z "0" "-1") (RangeDropLastOp z))
      |(rewrite (RangeOp z "-2" "-1") (RangeLastOp (RangeDropLastOp z)))
      |(rewrite (RangeFirstOp (EmptyZ)) (EmptyZ))
      |(rewrite (RangeFirstOp (TrieZ (Singleton p))) (TrieZ (Singleton p)))
      |(rewrite (RangeFirstOp (TrieZ (Union (Singleton (Eps)) rest))) (TrieZ (Singleton (Eps))))
      |(rewrite (RangeFirstOp (TrieZ (Union rest (Singleton (Eps))))) (TrieZ (Singleton (Eps))))
      |(rewrite
      |  (RangeFirstOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Concat (Item left) left-tail))
      |        (Singleton (Concat (Item right) right-tail)))))
      |  (TrieZ (Singleton (Concat (Item left) left-tail)))
      |  :when ((ordered-before left right)))
      |(rewrite
      |  (RangeFirstOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Concat (Item left) left-tail))
      |        (Singleton (Concat (Item right) right-tail)))))
      |  (TrieZ (Singleton (Concat (Item right) right-tail)))
      |  :when ((ordered-before right left)))
      |(rewrite
      |  (RangeFirstOp""".stripMargin

  private val part6: String =
    """      |    (TrieZ
      |      (Union
      |        (Singleton (Item left))
      |        (Singleton (Item right)))))
      |  (TrieZ (Singleton (Item left)))
      |  :when ((ordered-before left right)))
      |(rewrite
      |  (RangeFirstOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Item left))
      |        (Singleton (Item right)))))
      |  (TrieZ (Singleton (Item right)))
      |  :when ((ordered-before right left)))
      |(rewrite (RangeLastOp (EmptyZ)) (EmptyZ))
      |(rewrite (RangeLastOp (TrieZ (Singleton p))) (TrieZ (Singleton p)))
      |(rewrite (RangeLastOp (TrieZ (Union (Singleton (Eps)) (Singleton p)))) (TrieZ (Singleton p)))
      |(rewrite (RangeLastOp (TrieZ (Union (Singleton p) (Singleton (Eps))))) (TrieZ (Singleton p)))
      |(rewrite (RangeLastOp (TrieZ (Union (Singleton (Eps)) rest))) (RangeLastOp (TrieZ rest))
      |  :when ((nonempty-focus (TrieZ rest))))
      |(rewrite (RangeLastOp (TrieZ (Union rest (Singleton (Eps))))) (RangeLastOp (TrieZ rest))
      |  :when ((nonempty-focus (TrieZ rest))))
      |(rewrite
      |  (RangeLastOp (TrieZ (Union (Singleton (Eps)) (Union (Singleton left) (Singleton right)))))
      |  (RangeLastOp (TrieZ (Union (Singleton left) (Singleton right)))))
      |(rewrite
      |  (RangeLastOp (TrieZ (Union (Union (Singleton left) (Singleton right)) (Singleton (Eps)))))
      |  (RangeLastOp (TrieZ (Union (Singleton left) (Singleton right)))))
      |(rewrite
      |  (RangeLastOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Concat (Item left) left-tail))
      |        (Union
      |          (Singleton (Concat (Item mid) mid-tail))
      |          (Singleton (Concat (Item right) right-tail))))))
      |  (RangeLastOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Concat (Item mid) mid-tail))
      |        (Singleton (Concat (Item right) right-tail)))))
      |  :when ((ordered-before left right) (ordered-before mid right)))
      |(rewrite
      |  (RangeLastOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Concat (Item left) left-tail))
      |        (Singleton (Concat (Item right) right-tail)))))
      |  (TrieZ (Singleton (Concat (Item right) right-tail)))
      |  :when ((ordered-before left right)))
      |(rewrite
      |  (RangeLastOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Concat (Item left) left-tail))
      |        (Singleton (Concat (Item right) right-tail)))))
      |  (TrieZ (Singleton (Concat (Item left) left-tail)))
      |  :when ((ordered-before right left)))
      |(rewrite
      |  (RangeLastOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Item left))
      |        (Singleton (Item right)))))
      |  (TrieZ (Singleton (Item right)))
      |  :when ((ordered-before left right)))
      |(rewrite
      |  (RangeLastOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Item left))
      |        (Singleton (Item right)))))
      |  (TrieZ (Singleton (Item left)))
      |  :when ((ordered-before right left)))
      |(rewrite (RangeDropLastOp (EmptyZ)) (EmptyZ))
      |(rewrite (RangeDropLastOp (TrieZ (Singleton p))) (EmptyZ))
      |(rewrite (RangeDropLastOp (TrieZ (Union (Singleton (Eps)) (Singleton (Item item))))) (TrieZ (Singleton (Eps))))
      |(rewrite (RangeDropLastOp (TrieZ (Union (Singleton (Item item)) (Singleton (Eps))))) (TrieZ (Singleton (Eps))))
      |(rewrite (RangeDropLastOp (TrieZ (Union (Singleton (Eps)) (Singleton (Concat (Item item) rest))))) (TrieZ (Singleton (Eps))))
      |(rewrite (RangeDropLastOp (TrieZ (Union (Singleton (Concat (Item item) rest)) (Singleton (Eps))))) (TrieZ (Singleton (Eps))))
      |(rewrite
      |  (RangeDropLastOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Item left))
      |        (Singleton (Item right)))))
      |  (TrieZ (Singleton (Item left)))
      |  :when ((ordered-before left right)))
      |(rewrite
      |  (RangeDropLastOp
      |    (TrieZ
      |      (Union
      |        (Singleton (Item left))
      |        (Singleton (Item right)))))
      |  (TrieZ (Singleton (Item right)))
      |  :when ((ordered-before right left)))
        |(rewrite
        |  (RangeFirstOp
        |    (UnionOp
        |      (WrapOp left (Item left-key))
        |      (WrapOp right (Item right-key))))
        |  (WrapOp left (Item left-key))
        |  :when ((ordered-before left-key right-key)))
        |(rewrite
        |  (RangeFirstOp
        |    (UnionOp
        |      (WrapOp left (Item left-key))
        |      (WrapOp right (Item right-key))))
        |  (WrapOp right (Item right-key))
        |  :when ((ordered-before right-key left-key)))
        |(rewrite""".stripMargin

  private val part7: String =
    """        |  (RangeLastOp
        |    (UnionOp
        |      (WrapOp left (Item left-key))
        |      (WrapOp right (Item right-key))))
        |  (WrapOp right (Item right-key))
        |  :when ((ordered-before left-key right-key)))
        |(rewrite
        |  (RangeLastOp
        |    (UnionOp
        |      (WrapOp left (Item left-key))
        |      (WrapOp right (Item right-key))))
        |  (WrapOp left (Item left-key))
        |  :when ((ordered-before right-key left-key)))
        |(rewrite
        |  (RangeDropLastOp
        |    (UnionOp
        |      (WrapOp left (Item left-key))
        |      (WrapOp right (Item right-key))))
        |  (WrapOp left (Item left-key))
        |  :when ((ordered-before left-key right-key)))
        |(rewrite
        |  (RangeDropLastOp
        |    (UnionOp
        |      (WrapOp left (Item left-key))
        |      (WrapOp right (Item right-key))))
        |  (WrapOp right (Item right-key))
        |  :when ((ordered-before right-key left-key)))
        |(rewrite
        |  (RangeFirstOp
        |    (UnionOp
        |      (TrieZ (Singleton (Item left-key)))
        |      (TrieZ (Singleton (Item right-key)))))
        |  (TrieZ (Singleton (Item left-key)))
        |  :when ((ordered-before left-key right-key)))
        |(rewrite
        |  (RangeFirstOp
        |    (UnionOp
        |      (TrieZ (Singleton (Item left-key)))
        |      (TrieZ (Singleton (Item right-key)))))
        |  (TrieZ (Singleton (Item right-key)))
        |  :when ((ordered-before right-key left-key)))
        |(rewrite
        |  (RangeLastOp
        |    (UnionOp
        |      (TrieZ (Singleton (Item left-key)))
        |      (TrieZ (Singleton (Item right-key)))))
        |  (TrieZ (Singleton (Item right-key)))
        |  :when ((ordered-before left-key right-key)))
        |(rewrite
        |  (RangeLastOp
        |    (UnionOp
        |      (TrieZ (Singleton (Item left-key)))
        |      (TrieZ (Singleton (Item right-key)))))
        |  (TrieZ (Singleton (Item left-key)))
        |  :when ((ordered-before right-key left-key)))
        |(rewrite
        |  (RangeDropLastOp
        |    (UnionOp
        |      (TrieZ (Singleton (Item left-key)))
        |      (TrieZ (Singleton (Item right-key)))))
        |  (TrieZ (Singleton (Item left-key)))
        |  :when ((ordered-before left-key right-key)))
        |(rewrite
        |  (RangeDropLastOp
        |    (UnionOp
        |      (TrieZ (Singleton (Item left-key)))
        |      (TrieZ (Singleton (Item right-key)))))
        |  (TrieZ (Singleton (Item right-key)))
        |  :when ((ordered-before right-key left-key)))
        |(rewrite (RangeFirstOp (WrapOp src prefix)) (WrapOp (RangeFirstOp src) prefix))
        |(rewrite (RangeLastOp (WrapOp src prefix)) (WrapOp (RangeLastOp src) prefix))
        |(rewrite (RangeDropLastOp (WrapOp src prefix)) (WrapOp (RangeDropLastOp src) prefix))
        |(rewrite (RangeOp (TrieZ (Singleton p)) "0" "2") (TrieZ (Singleton p)))
      |(rewrite (RangeOp (TrieZ (Singleton p)) "1" "2") (EmptyZ))
      |(rewrite (RangeOp (TrieZ (Singleton p)) "-2" "0") (TrieZ (Singleton p)))
      |(rewrite (RangeOp (TrieZ (Singleton p)) "-2" "-1") (EmptyZ))
      |(rewrite (RangeOp (RangeOp z "0" "2") "0" "1") (RangeOp z "0" "1"))
      |(rewrite (RangeOp (RangeOp z "0" "2") "1" "2") (RangeOp z "1" "2"))
      |(rewrite (RangeOp (RangeOp z "0" "1") "1" "2") (EmptyZ))
      |(rewrite (RangeOp (RangeOp z "-2" "0") "-1" "0") (RangeOp z "-1" "0"))
      |(rewrite (RangeOp (RangeOp z "0" "-1") "0" "0") (RangeOp z "0" "-1"))
      |(rewrite (RangeOp (WrapOp src prefix) "0" "1") (WrapOp (RangeFirstOp src) prefix))
      |(rewrite (RangeOp (WrapOp src prefix) "-1" "0") (WrapOp (RangeLastOp src) prefix))
      |(rewrite (RangeOp (WrapOp src prefix) "0" "-1") (WrapOp (RangeDropLastOp src) prefix))
      |(rewrite (HeadOp (EmptyZ)) (EmptyZ))
      |(rewrite (HeadOp (TrieZ (Empty))) (EmptyZ))
      |(rewrite (HeadOp (TrieZ (Singleton (Eps)))) (EmptyZ))
      |(rewrite (HeadOp (TrieZ (Singleton (Item head)))) (TrieZ (Singleton (Item head))))
      |(rewrite (HeadOp (TrieZ (Singleton (Concat (Item head) rest)))) (TrieZ (Singleton (Item head))))
      |(rewrite (HeadOp (TrieZ (Union a b))) (UnionOp (HeadOp (TrieZ a)) (HeadOp (TrieZ b))))""".stripMargin

  private val part8: String =
    """      |(rewrite (HeadOp (UnionOp a b)) (UnionOp (HeadOp a) (HeadOp b)))
      |(rewrite (HeadOp (JoinAllOp3 a b c)) (JoinAllOp3 (HeadOp a) (HeadOp b) (HeadOp c)))
      |(rewrite (HeadOp (NonEmptyOp z)) (HeadOp z))
      |(rewrite (HeadOp (WrapOp src (Eps))) (HeadOp src))
      |(rewrite (HeadOp (WrapOp src (Item head))) (TrieZ (Singleton (Item head))) :when ((nonempty-focus src)))
      |(rewrite (HeadOp (WrapOp src (Concat (Item head) rest))) (TrieZ (Singleton (Item head))) :when ((nonempty-focus src)))
        |(rewrite (HeadOp (MemoZ z)) (MemoZ (HeadOp z)))
          |(rewrite (IterOp z (TailTemplate)) (TailsUnionOp z))
          |(rewrite (IterOp z (HeadTemplate)) (HeadOp z))
          |(rewrite (IterOp z (ReconstructTemplate)) (NonEmptyOp z))
          |(rewrite (IterOp z (PrefixedReconstructTemplate prefix)) (WrapOp (NonEmptyOp z) prefix))
          |(rewrite (IterOp z (RangeTailTemplate start end)) (IterRangeTailOp z start end))
          |(rewrite (IterOp z (RangeReconstructTemplate start end)) (IterRangeReconstructOp z start end))
          |(rewrite (IterOp z (PrefixedRangeReconstructTemplate prefix start end)) (IterPrefixedRangeReconstructOp z prefix start end))
          |(rewrite (FixpointOp z (TailTemplate)) (TailsClosureOp z))
          |(rewrite (FixpointOp z (HeadTemplate)) (UnionOp z (HeadOp z)))
          |(rewrite (FixpointOp z (ReconstructTemplate)) z)
          |(rewrite (FixpointOp z (PrefixedReconstructTemplate (Eps))) z)
          |(rewrite (FixpointOp z (RangeTailTemplate "0" "0")) (TailsClosureOp z))
          |(rewrite (FixpointOp z (RangeTailTemplate "1" "1")) z)
          |(rewrite (FixpointOp z (RangeReconstructTemplate start end)) z)
          |(rewrite (FixpointOp z (PrefixedRangeReconstructTemplate (Eps) start end)) z)
          |(rewrite (Child item (IterOp src (TailTemplate))) (FrontierChildUnionOp (FrontierUnionOp src) item))
          |(rewrite (Child item (IterOp src (HeadTemplate))) (Child item (HeadOp src)))
          |(rewrite (Child item (IterOp src (ReconstructTemplate))) (Child item (NonEmptyOp src)))
          |(rewrite (Child item (IterOp src (PrefixedReconstructTemplate prefix))) (Child item (WrapOp (NonEmptyOp src) prefix)))
          |(rewrite (Child item (IterOp src (RangeTailTemplate start end))) (FrontierChildUnionOp (IterRangeTailOp src start end) item))
          |(rewrite (Child item (IterOp src (RangeReconstructTemplate start end))) (FrontierChildUnionOp (IterRangeReconstructOp src start end) item))
          |(rewrite (Child item (IterOp src (PrefixedRangeReconstructTemplate prefix start end))) (FrontierChildUnionOp (IterPrefixedRangeReconstructOp src prefix start end) item))
          |(rewrite (Child item (FixpointOp src (TailTemplate))) (FrontierStateOp (FrontierTailUnionOp (TailsClosureOp src) item)))
          |(rewrite (Child item (FixpointOp src (HeadTemplate))) (Child item (UnionOp src (HeadOp src))))
          |(rewrite (Child item (FixpointOp src (ReconstructTemplate))) (Child item src))
          |(rewrite (Child item (FixpointOp src (PrefixedReconstructTemplate (Eps)))) (Child item src))
          |(rewrite (Child item (FixpointOp src (RangeTailTemplate "0" "0"))) (FrontierStateOp (FrontierTailUnionOp (TailsClosureOp src) item)))
          |(rewrite (Child item (FixpointOp src (RangeTailTemplate "1" "1"))) (Child item src))
          |(rewrite (Child item (FixpointOp src (RangeReconstructTemplate start end))) (Child item src))
          |(rewrite (Child item (FixpointOp src (PrefixedRangeReconstructTemplate (Eps) start end))) (Child item src))
        |(rewrite (TailsUnionOp src) (FrontierUnionOp src))
        |
      |(rewrite (Child item (EmptyZ)) (EmptyZ))
      |(rewrite (Child item (TrieZ (Empty))) (EmptyZ))
      |(rewrite (Child item (TrieZ (Singleton (Eps)))) (EmptyZ))
      |(rewrite (Child item (TrieZ (Singleton (Item item)))) (TrieZ (Singleton (Eps))))
      |(rewrite (Child item (TrieZ (Singleton (Item other)))) (EmptyZ) :when ((!= item other)))
      |(rewrite (Child item (TrieZ (Singleton (Concat (Item item) rest)))) (TrieZ (Singleton rest)))
      |(rewrite (Child item (TrieZ (Singleton (Concat (Item other) rest)))) (EmptyZ) :when ((!= item other)))
      |(rewrite (Child item (TrieZ (Union a b))) (UnionOp (Child item (TrieZ a)) (Child item (TrieZ b))))
      |(rewrite (Child item (MemoZ z)) (MemoZ (Child item z)))
      |(rewrite (Child item (UnionOp a b)) (UnionOp (Child item a) (Child item b)))
      |(rewrite (Child item (JoinAllOp3 a b c)) (JoinAllOp3 (Child item a) (Child item b) (Child item c)))
      |(rewrite (Child item (IntersectionOp a b)) (IntersectionOp (Child item a) (Child item b)))
      |(rewrite (Child item (MeetAllOp3 a b c)) (MeetAllOp3 (Child item a) (Child item b) (Child item c)))
      |(rewrite (Child item (DiffOp a b)) (DiffOp (Child item a) (Child item b)))
      |(rewrite (Child item (RestrictionOp src (TrieZ (Singleton (Eps))))) (Child item src))
      |(rewrite (Child item (RestrictionOp src (UnionOp (TrieZ (Singleton (Eps))) prefixes))) (Child item src))
      |(rewrite (Child item (RestrictionOp src (UnionOp prefixes (TrieZ (Singleton (Eps)))))) (Child item src))
      |(rewrite (Child item (RestrictionOp src (TrieZ (Singleton (Item item))))) (RestrictionOp (Child item src) (TrieZ (Singleton (Eps)))))
      |(rewrite (Child item (RestrictionOp src (TrieZ (Singleton (Item head))))) (EmptyZ) :when ((!= item head)))
      |(rewrite (Child item (RestrictionOp src (TrieZ (Singleton (Concat (Item head) rest))))) (RestrictionOp (Child item src) (Child item (TrieZ (Singleton (Concat (Item head) rest))))))
      |(rewrite (Child item (RestrictionOp src (TrieZ (Union p q)))) (RestrictionOp (Child item src) (Child item (TrieZ (Union p q)))))
      |(rewrite (Child item (RaffinationOp src prefixes)) (Child item (DiffOp src (RestrictionOp src prefixes))))
      |(rewrite (Child item (WrapOp z (Eps))) (Child item z))
      |(rewrite (Child item (WrapOp z (Item item))) z)
      |(rewrite (Child item (WrapOp z (Item other))) (EmptyZ) :when ((!= item other)))
      |(rewrite (Child item (WrapOp z (Concat (Item item) rest))) (WrapOp z rest))
      |(rewrite (Child item (WrapOp z (Concat (Item other) rest))) (EmptyZ) :when ((!= item other)))
      |(rewrite (UnwrapOp z (Item item)) (Child item z))
      |(rewrite (UnwrapOp z (Concat (Item item) rest)) (UnwrapOp (Child item z) rest))
      |(rewrite (Child item (NonEmptyOp z)) (Child item z))
          |(rewrite (Child item (FrontierUnionOp src)) (FrontierChildUnionOp (FrontierUnionOp src) item))
          |(rewrite (Child item (FrontierTailUnionOp src previous)) (FrontierChildUnionOp (FrontierTailUnionOp src previous) item))
          |(rewrite (Child item (FrontierChildUnionOp src previous)) (FrontierChildUnionOp (FrontierChildUnionOp src previous) item))
          |(rewrite (Child item (FrontierStateOp active)) (FrontierStateOp (FrontierChildUnionOp active item)))
          |(rewrite (Child item (IterRangeTailOp src start end)) (FrontierChildUnionOp (IterRangeTailOp src start end) item))
          |(rewrite (Child item (IterRangeReconstructOp src start end)) (FrontierChildUnionOp (IterRangeReconstructOp src start end) item))
          |(rewrite (Child item (IterPrefixedRangeReconstructOp src prefix start end)) (FrontierChildUnionOp (IterPrefixedRangeReconstructOp src prefix start end) item))
          |(rewrite (Child item (PrefixClosureOp z)) (PrefixClosureBelowOp (Child item z)))
        |(rewrite (Child item (PrefixClosureBelowOp z)) (PrefixClosureBelowOp (Child item z)))
        |(rewrite (Child item (SuffixClosureOp z)) (FrontierStateOp (FrontierTailUnionOp (SuffixClosureOp z) item)))
        |(rewrite (Child item (TailsClosureOp z)) (FrontierStateOp (FrontierTailUnionOp (TailsClosureOp z) item)))
      |(rewrite (Child item (RangeLastOp (TrieZ (Union (Singleton (Eps)) rest)))) (Child item (RangeLastOp (TrieZ rest)))
      |  :when ((nonempty-focus (TrieZ rest))))
      |(rewrite (Child item (RangeLastOp (TrieZ (Union rest (Singleton (Eps)))))) (Child item (RangeLastOp (TrieZ rest)))
      |  :when ((nonempty-focus (TrieZ rest))))
      |(rewrite
      |  (Child right
      |    (RangeLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Eps))
      |          (Union
      |            (Singleton (Concat (Item left) left-tail))
      |            (Union
      |              (Singleton (Concat (Item mid) mid-tail))
      |              (Singleton (Concat (Item right) right-tail))))))))
      |  (TrieZ (Singleton right-tail))
      |  :when ((ordered-before left right) (ordered-before mid right)))
      |(rewrite
      |  (Child item
      |    (RangeLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Eps))
      |          (Union
      |            (Singleton (Concat (Item left) left-tail))
      |            (Union
      |              (Singleton (Concat (Item mid) mid-tail))
      |              (Singleton (Concat (Item right) right-tail))))))))
      |  (EmptyZ)
      |  :when ((ordered-before left right) (ordered-before mid right) (!= item right)))
      |(rewrite
      |  (Child item
      |    (RangeLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Concat (Item left) left-tail))
      |          (Union
      |            (Singleton (Concat (Item mid) mid-tail))
      |            (Singleton (Concat (Item right) right-tail)))))))
      |  (Child item
      |    (RangeLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Concat (Item mid) mid-tail))
      |          (Singleton (Concat (Item right) right-tail))))))
      |  :when ((ordered-before left right) (ordered-before mid right)))
      |(rewrite
      |  (Child right
      |    (RangeLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Concat (Item left) left-tail))
      |          (Singleton (Concat (Item right) right-tail))))))
      |  (TrieZ (Singleton right-tail))
      |  :when ((ordered-before left right)))
      |(rewrite
      |  (Child item
      |    (RangeLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Concat (Item left) left-tail))
      |          (Singleton (Concat (Item right) right-tail))))))
      |  (EmptyZ)
      |  :when ((ordered-before left right) (!= item right)))
      |(rewrite
      |  (Child left
      |    (RangeLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Concat (Item left) left-tail))
      |          (Singleton (Concat (Item right) right-tail))))))
      |  (TrieZ (Singleton left-tail))
      |  :when ((ordered-before right left)))
      |(rewrite
      |  (Child item
      |    (RangeLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Concat (Item left) left-tail))
      |          (Singleton (Concat (Item right) right-tail))))))
      |  (EmptyZ)
      |  :when ((ordered-before right left) (!= item left)))
      |(rewrite
      |  (Child item
      |    (RangeLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Concat (Item item) left-tail))
      |          (Singleton (Concat (Item item) right-tail))))))
      |  (RangeLastOp (TrieZ (Union (Singleton left-tail) (Singleton right-tail)))))
      |(rewrite
      |  (Child item
      |    (RangeLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Concat (Item head) left-tail))
      |          (Singleton (Concat (Item head) right-tail))))))
      |  (EmptyZ)
      |  :when ((!= item head)))
      |(rewrite
      |  (Child left
      |    (RangeDropLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Eps))
      |          (Union
      |            (Singleton (Concat (Item left) left-tail))
      |            (Union
      |              (Singleton (Concat (Item mid) mid-tail))
      |              (Singleton (Concat (Item right) right-tail))))))))
      |  (Child left
      |    (TrieZ
      |      (Union
      |        (Singleton (Eps))
      |        (Union
      |          (Singleton (Concat (Item left) left-tail))
      |          (Union
      |            (Singleton (Concat (Item mid) mid-tail))
      |            (Singleton (Concat (Item right) right-tail)))))))
      |  :when ((ordered-before left right) (ordered-before mid right)))
      |(rewrite
      |  (Child mid
      |    (RangeDropLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Eps))
      |          (Union
      |            (Singleton (Concat (Item left) left-tail))
      |            (Union
      |              (Singleton (Concat (Item mid) mid-tail))
      |              (Singleton (Concat (Item right) right-tail))))))))
      |  (Child mid
      |    (TrieZ
      |      (Union
      |        (Singleton (Eps))
      |        (Union
      |          (Singleton (Concat (Item left) left-tail))
      |          (Union
      |            (Singleton (Concat (Item mid) mid-tail))
      |            (Singleton (Concat (Item right) right-tail)))))))
      |  :when ((ordered-before left right) (ordered-before mid right)))
      |(rewrite
      |  (Child right
      |    (RangeDropLastOp
      |      (TrieZ
      |        (Union
      |          (Singleton (Eps))
      |          (Union
      |            (Singleton (Concat (Item left) left-tail))
      |            (Union
      |              (Singleton (Concat (Item mid) mid-tail))
      |              (Singleton (Concat (Item right) right-tail))))))))
      |  (EmptyZ)
      |  :when ((ordered-before left right) (ordered-before mid right)))
      |(rewrite
      |  (Child item
      |    (RangeLastOp
      |      (RangeDropLastOp
      |        (TrieZ
      |          (Union
      |            (Singleton (Eps))
      |            (Union
      |              (Singleton (Concat (Item item) left-tail))
      |              (Union
      |                (Singleton (Concat (Item item) mid-tail))
      |                (Singleton (Concat (Item right) right-tail)))))))))
      |  (RangeLastOp (TrieZ (Union (Singleton left-tail) (Singleton mid-tail))))
      |  :when ((ordered-before item right)))
      |(rewrite
      |  (Child right
      |    (RangeLastOp
      |      (RangeDropLastOp
      |        (TrieZ
      |          (Union
      |            (Singleton (Eps))
      |            (Union
      |              (Singleton (Concat (Item left) left-tail))
      |              (Union
      |                (Singleton (Concat (Item mid) mid-tail))
      |                (Singleton (Concat (Item right) right-tail)))))))))
      |  (EmptyZ)
      |  :when ((ordered-before left right) (ordered-before mid right)))
      |(rewrite (Child item (RangeOp z "0" "0")) (Child item z))
      |(rewrite (Child item (RangeOp z "1" "1")) (EmptyZ))
      |(rewrite (Child item (ConcatOp left right))
      |  (UnionOp
      |    (TerminalProductChild item left right)
      |    (ConcatOp (Child item left) right)))
      |(rewrite (TerminalProductChild item left right) (Child item right) :when ((terminal left)))
      |(rewrite (TerminalProductChild item left right) (EmptyZ) :when ((nonterminal left)))
      |(rewrite (TerminalProductChild item (EmptyZ) right) (EmptyZ))
      |(rewrite (TerminalProductChild item (TrieZ (Empty)) right) (EmptyZ))
      |(rewrite (TerminalProductChild item (TrieZ (Singleton (Eps))) right) (Child item right))
      |(rewrite (TerminalProductChild item (TrieZ (Singleton (Item head))) right) (EmptyZ))
      |(rewrite (TerminalProductChild item (TrieZ (Singleton (Concat (Item head) rest))) right) (EmptyZ))
      |(rewrite (TerminalProductChild item (UnionOp a b) right) (UnionOp (TerminalProductChild item a right) (TerminalProductChild item b right)))
      |(rewrite (TerminalProductChild item (WrapOp z (Eps)) right) (TerminalProductChild item z right))
      |(rewrite (TerminalProductChild item (WrapOp z (Item head)) right) (EmptyZ))
      |(rewrite (TerminalProductChild item (WrapOp z (Concat (Item head) rest)) right) (EmptyZ))
      |""".stripMargin

  def program: String =
    Vector(
      part0,
      part1,
      part2,
      part3,
      part4,
      part5,
      part6,
      part7,
      part8
    ).mkString("\n")
