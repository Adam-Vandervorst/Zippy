% =============================================================================
% TIER 3 module: THE INJECTIVE-IMAGE COUNTING PRINCIPLE.  Include after
% `_signature.p`, `_paths.p` and `_card.p`.
%
% Split out of `_card.p` because it is the only counting axiom that mentions
% PATH STRUCTURE (`app`), so a purely lattice-theoretic cardinality file such as
% `card_subadd.p` must not — and now cannot — pull it in (before the split it
% could not even be PARSED there: `app` is undeclared without `_paths.p`).  See `_card.p`'s
% header for what is assumed and what is derived.
% =============================================================================

% ---- the injective-image principle, with path maps reified into `pmap` -------
tff(pmap_type,    type, pmap:    $tType ).
tff(apm_type,     type, apm:     ( pmap * path ) > path ).
tff(injOn_type,   type, injOn:   ( pmap * space ) > $o ).
tff(isImage_type, type, isImage: ( pmap * space * space ) > $o ).
tff(pfxmap_type,  type, pfxmap:  path > pmap ).

tff(injOn_def, axiom,
    ! [F: pmap, A: space] :
      ( injOn(F,A)
    <=> ! [P: path, Q: path] :
          ( ( mem(P,A) & mem(Q,A) & apm(F,P) = apm(F,Q) ) => P = Q ) ) ).

tff(isImage_def, axiom,
    ! [F: pmap, A: space, B: space] :
      ( isImage(F,A,B)
    <=> ! [Y: path] : ( mem(Y,B) <=> ? [X: path] : ( mem(X,A) & apm(F,X) = Y ) ) ) ).

tff(card_image, axiom,
    ! [F: pmap, A: space, B: space] :
      ( ( injOn(F,A) & isImage(F,A,B) ) => card(B) = card(A) ) ).

% comprehension: the prefix map q |-> app(W,q) exists as an object of sort pmap
tff(pfxmap_def, axiom,
    ! [W: path, Q: path] : apm(pfxmap(W), Q) = app(W,Q) ).
