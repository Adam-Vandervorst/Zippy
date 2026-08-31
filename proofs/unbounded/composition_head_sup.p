% ===========================================================================
% TIER 3 / composition / tails-union.
%
% ONE TRIE LEVEL DOWN THROUGH A PRODUCT.  Taking the tails of a composition
% splits on whether the LEFT factor contains the empty path:
%
%   eps in A   =>  tu(A . B) = (tu(A) . B)  u  tu(B)
%   eps not in A  =>  tu(A . B) = tu(A) . B
%
% because a non-empty path of `A . B` is `q ++ r` with q in A and r in B, and
% the certified append-cons split (proofs/lemma_append_cons.smt2, imported as
% `_appsplit.p`) says its head either belongs to q — leaving `tail(q) ++ r`, a
% path of `tu(A) . B` — or q is empty and the whole path is r, leaving a path of
% `tu(B)`.  This is the only theorem in the corpus that needs that lemma, which
% is why `_appsplit.p` is a module of its own.
%
% This is exactly the case analysis a trie backend performs when it descends one
% level into a product node, and the `eps in A` guard is the degenerate shape
% docs/traps.md 1 puts first: `{eps}` is not `{}`, and a left factor containing
% the empty path contributes the WHOLE right factor's tails at every level.
%
% GENERALISES: proofs/composition.smt2 / proofs/composition_norm.smt2, which
% certify the same decomposition for one concrete pair of literal spaces; and
% tier-1's TailsUnion-of-Composition path, which simply widens to [0, hi].
%
%
% THIS FILE: THE TWO REVERSE INCLUSIONS.  Both hold with no case analysis and no
% split lemma: prepending a head to `q2 ++ r` is `(h::q2) ++ r`, so a path of
% `tu(A) . B` is always a tail of `A . B`; and if eps is in A then B is a subset
% of `A . B`, so every tail of B is a tail of the product.
%
% VERDICT: PROVED by vampire in 0.7s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_tails_ops.p').
include('_concat_ops.p').

tff(a0_type, type, a0: space ).
tff(b0_type, type, b0: space ).

tff(composition_head_sup, conjecture,
    ( sub(comp(tu(a0), b0), tu(comp(a0,b0)))
    & ( mem(nil,a0) => sub(tu(b0), tu(comp(a0,b0))) ) ) ).
