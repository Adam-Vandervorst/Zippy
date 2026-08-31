% =============================================================================
% TIER 3 module: THE PREFIX RELATION.  Include after `_signature.p` and
% `_paths.p`.
%
% `isPrefix` exactly as `EquivPipeline.foPrelude` axiomatises it for the
% instance tier, PLUS the equivalent existential characterisation
% `isPrefix(P,Q) <=> ?R. app(P,R) = Q`.  The two agree; the existential form is
% the one the restriction / raffination theorems actually use, and the
% recursive form is what keeps the corpus in step with the SMT prelude the rest
% of the repository proves against.
% =============================================================================

% isPrefix, exactly as EquivPipeline.foPrelude axiomatises it, plus the
% equivalent existential characterisation (`isPrefix_app` is the form the
% restriction / composition theorems actually use; the two agree).
tff(pfx_nil,      axiom, ! [P: path] : isPrefix(nil, P) ).
tff(pfx_cons_nil, axiom, ! [H: item, T: path] : ~ isPrefix(cons(H,T), nil) ).
tff(pfx_cons,     axiom,
    ! [H: item, T: path, H2: item, T2: path] :
      ( isPrefix(cons(H,T), cons(H2,T2)) <=> ( H = H2 & isPrefix(T,T2) ) ) ).
tff(isPrefix_app, axiom,
    ! [P: path, Q: path] : ( isPrefix(P,Q) <=> ? [R: path] : app(P,R) = Q ) ).
