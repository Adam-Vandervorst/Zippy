% =============================================================================
% TIER 3 module: THE APPEND-CONS SPLIT LEMMA.  Include after `_signature.p` and
% `_paths.p`.
%
% This is the certified lemma of proofs/lemma_append_cons.smt2 (PROVED — see
% proofs/STATUS.tsv), the workhorse that lets a first-order prover take an
% `app(Q,R)` apart WITHOUT induction: a non-empty append either has the whole
% cons on the right with an empty left factor, or the head belongs to the left
% factor and the tails append.
%
% Kept in its own module because it is an expensive biconditional with a nested
% existential and exactly ONE theorem needs it — `composition_head_split.p`, the
% pointwise decomposition of the tails of a product.  See the module list in
% `_signature.p` for why every axiom in scope is paid for.
% =============================================================================

% certified lemma proofs/lemma_append_cons.smt2 (PROVED): the append-cons split.
% This is the workhorse that lets a first-order prover take `app(Q,R)` apart
% without induction.
tff(app_cons_split, axiom,
    ! [K: item, P: path, Q: path, R: path] :
      ( cons(K,P) = app(Q,R)
    <=> ( ( Q = nil & R = cons(K,P) )
        | ? [Q2: path] : ( Q = cons(K,Q2) & P = app(Q2,R) ) ) ) ).
