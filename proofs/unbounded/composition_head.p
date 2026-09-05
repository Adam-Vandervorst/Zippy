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
% THIS FILE: THE TWO EQUALITIES, assembled from the pointwise decomposition
% (`composition_head_split.p`, PROVED) and the two reverse inclusions
% (`composition_head_sup.p`, PROVED), both imported as staged premises.  Same
% staging discipline as `iteration_split.p`, and for the same measured reason:
% the equational goal does not close on its own.
%
% VERDICT: PROVED by vampire in 0.2s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_lattice_lemmas.p').
include('_paths.p').
include('_appsplit.p').
include('_tails_ops.p').
include('_concat_ops.p').

tff(a0_type, type, a0: space ).
tff(b0_type, type, b0: space ).

% --- staged lemmas, each PROVED in its own file
tff(head_split, axiom,
    ! [T: path] :
      ( mem(T, tu(comp(a0,b0)))
     => ( mem(T, comp(tu(a0), b0)) | ( mem(nil,a0) & mem(T, tu(b0)) ) ) ) ).
tff(head_sup1, axiom, sub(comp(tu(a0), b0), tu(comp(a0,b0))) ).
tff(head_sup2, axiom, ( mem(nil,a0) => sub(tu(b0), tu(comp(a0,b0))) ) ).

tff(composition_head, conjecture,
    ( ( mem(nil,a0) => tu(comp(a0,b0)) = cup(comp(tu(a0), b0), tu(b0)) )
    & ( ~ mem(nil,a0) => tu(comp(a0,b0)) = comp(tu(a0), b0) ) ) ).
