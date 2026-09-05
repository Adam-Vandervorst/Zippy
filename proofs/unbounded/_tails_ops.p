% =============================================================================
% TIER 3 operator module: TAILS-UNION, TAILS-INTERSECTION and head groups.
% Include after `_signature.p`.
%
%   TailsUnion(s)        = { t : SOME h with h::t in s }
%   TailsIntersection(s) = { t : s has AT LEAST ONE head, and for EVERY head h
%                                of s, h::t in s }
%   headed(h,s)          = h is a head of s   (eval's groupMap key)
%   grp(h,s)             = the `rest` space of head group h
%
% The first conjunct of `ti_def` is not decoration: docs/traps.md 1 ("never
% confuse {} with {eps}") is exactly this arm.  eval writes
% `if groups.isEmpty then Set.empty else groups.valuesIterator...reduce(_ intersect _)`,
% so an empty space AND a space of only-empty-paths both give EMPTY — never
% "every tail", which is what dropping the conjunct would mean.
% =============================================================================

tff(tu_type,     type, tu:     space > space ).                 % Space.TailsUnion
tff(ti_type,     type, ti:     space > space ).                 % Space.TailsIntersection
tff(headed_type, type, headed: ( item * space ) > $o ).
tff(grp_type,    type, grp:    ( item * space ) > space ).

% den: `(exists ((h Int)) (m_src (cons h p)))`
tff(tu_def, axiom,
    ! [P: path, A: space] : ( mem(P, tu(A)) <=> ? [H: item] : mem(cons(H,P), A) ) ).

tff(headed_def, axiom,
    ! [H: item, A: space] : ( headed(H,A) <=> ? [Q: path] : mem(cons(H,Q), A) ) ).

% eval: `groups = recs(src).collect { case PathValue(h::tail) => h -> tail }.groupMap(_._1)(_._2)`
tff(grp_def, axiom,
    ! [T: path, H: item, A: space] : ( mem(T, grp(H,A)) <=> mem(cons(H,T), A) ) ).

% den: `(and (exists h,q. src(cons h q)) (forall h. (exists q. src (cons h q)) => src (cons h p)))`
tff(ti_def, axiom,
    ! [P: path, A: space] :
      ( mem(P, ti(A))
    <=> ( ( ? [H: item] : headed(H,A) )
        & ! [H: item] : ( headed(H,A) => mem(cons(H,P), A) ) ) ) ).
