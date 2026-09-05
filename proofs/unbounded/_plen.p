% =============================================================================
% TIER 3 module: PATH LENGTH.  Include after `_signature.p`, `_paths.p` and
% `_nat.p`.
%
% `plen : path > num` is the additive monoid morphism from paths to the ordered
% commutative monoid of `_nat.p`.  It is the object-level counterpart of
% `PathValue.items.length`, which is what tier-1 `Lower.lenBounds` and tier-2
% `LenZ3` propagate intervals over.
%
% NOTE `plen` lands in `num`, NOT in `$int`: see `_nat.p` for the measured
% reason (vampire 5.1.0 refutes `_signature.p + _paths.p + _plen.p` outright
% when `plen` is `$int`-valued, using only its own internally introduced theory
% axioms).  `plen_nonneg` is `le(zero, plen(P))`, which is already an axiom of
% `_nat.p` for every element of `num`, so it is not repeated here.
% =============================================================================

tff(plen_type, type, plen: path > num ).

tff(plen_nil,  axiom, plen(nil) = zero ).
tff(plen_cons, axiom, ! [H: item, T: path] : plen(cons(H,T)) = plus(plen(T), one) ).
tff(plen_app,  axiom, ! [P: path, Q: path] : plen(app(P,Q)) = plus(plen(P), plen(Q)) ).
