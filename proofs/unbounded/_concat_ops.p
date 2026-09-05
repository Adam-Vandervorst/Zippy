% =============================================================================
% TIER 3 operator module: COMPOSITION, WRAP, UNWRAP.  Include after
% `_signature.p`.  Each axiom is the corresponding arm of
% `EquivPipeline.Smt.den` / `eval`.
%
%   Composition(a,b) = { q++r : q in a, r in b }
%   Wrap(s,p)        = { p++q : q in s }        (eval: Composition(Singleton(p), s))
%   Unwrap(s,p)      = { q : p++q in s }
%
% NOTE the ASYMMETRY that docs/traps.md 4 records as a real historical bug
% ("UnwrapConcat_Unwraps stripped Concat-prefix factors in reversed order"):
% wrap composes its prefixes on the LEFT and unwrap on the RIGHT, so
% wrap(wrap(A,U),V) = wrap(A, app(V,U)) while unwrap(unwrap(A,U),V) =
% unwrap(A, app(U,V)).  Both are conjectures in `wrap_nest.p` precisely so the
% order is machine-checked rather than eyeballed, and the two REVERSED forms are
% negative controls (negative/not_wrap_nest_reversed.p and
% negative/not_unwrap_nest_reversed.p) that must NOT be provable.
% =============================================================================

tff(comp_type,   type, comp:   ( space * space ) > space ).     % Space.Composition
tff(wrap_type,   type, wrap:   ( space * path ) > space ).      % Space.Wrap
tff(unwrap_type, type, unwrap: ( space * path ) > space ).      % Space.Unwrap

% den: `(exists ((q Path) (r Path)) (and (= p (append q r)) (m_a q) (m_b r)))`
tff(comp_def, axiom,
    ! [P: path, A: space, B: space] :
      ( mem(P, comp(A,B))
    <=> ? [Q: path, R: path] : ( P = app(Q,R) & mem(Q,A) & mem(R,B) ) ) ).

% den: `(exists ((q Path)) (and (= p (W ++ q)) (m_src q)))`
tff(wrap_def, axiom,
    ! [P: path, A: space, W: path] :
      ( mem(P, wrap(A,W)) <=> ? [Q: path] : ( P = app(W,Q) & mem(Q,A) ) ) ).

% den: `(m_src (W ++ p))`
tff(unwrap_def, axiom,
    ! [P: path, A: space, W: path] : ( mem(P, unwrap(A,W)) <=> mem(app(W,P), A) ) ).
