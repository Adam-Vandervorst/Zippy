% =============================================================================
% TIER 3 module: LENGTH-BOUND PREDICATES.  Include after `_signature.p`,
% `_paths.p`, `_nat.p` and `_plen.p`.
%
%   lenLB(A,N)   every path of A is at least N items long
%   lenUB(A,N)   every path of A is at most  N items long
%
% These are the object-level form of the two endpoints of tier-1's
% `Lower.LenBounds` — there a pair of `Long`s attached to one AST node, here a
% predicate that can be quantified over ALL spaces and ALL N, which is the whole
% difference between tier-1/tier-2 and this tier.  Note both are VACUOUSLY TRUE
% on the empty space, exactly as `Lower.lenBounds` reports `EMPTY` for it.
% =============================================================================

tff(lenLB_type, type, lenLB: ( space * num ) > $o ).
tff(lenUB_type, type, lenUB: ( space * num ) > $o ).

tff(lenLB_def, axiom,
    ! [A: space, N: num] :
      ( lenLB(A,N) <=> ! [P: path] : ( mem(P,A) => le(N, plen(P)) ) ) ).
tff(lenUB_def, axiom,
    ! [A: space, N: num] :
      ( lenUB(A,N) <=> ! [P: path] : ( mem(P,A) => le(plen(P), N) ) ) ).
