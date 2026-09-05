% ===========================================================================
% TIER 3 / tails-union / unwrap.
%
% A SINGLE-ITEM WRAP IS UNDONE BY TAILS-UNION, and unwrapping by a
% single-item path IS that head's group: `tu(wrap(A, h::eps)) = A` and
% `unwrap(A, h::eps) = grp(h, A)`.  These are the two identities the trie
% backends use to descend one level, and they are the reason a one-level
% descend/ascend pair is free rather than a re-traversal.
%
% GENERALISES: TailsUnion_Iteration and the single-head unwrap fast path in
% the trie backends
%
% VERDICT: PROVED by vampire in 0.2s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_tails_ops.p').
include('_concat_ops.p').

tff(tails_union_wrap, conjecture,
    ! [A: space, H: item] :
      ( tu(wrap(A, cons(H,nil))) = A
      & unwrap(A, cons(H,nil)) = grp(H,A) ) ).
