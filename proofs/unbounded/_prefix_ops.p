% =============================================================================
% TIER 3 operator module: RESTRICTION and RAFFINATION.  Include after
% `_signature.p`.  Both axioms are the corresponding arm of
% `EquivPipeline.Smt.den`, which is the arm of `eval` in MORKL.scala.
%
%   Restriction(x,y) = { p in x : SOME PREFIX of p is in y }
%   Raffination(x,y) = x  minus  Restriction(x,y)      -- definitional
%
% Raffination is stated as the EQUATION, not re-derived: `eval` literally
% computes `recs(Space.Subtraction(x_e, Space.Restriction(x_e, y_e)))`, so the
% partition theorem in raffination.p is a theorem about restriction, not a
% restatement of the raffination axiom.
% =============================================================================

tff(restr_type, type, restr: ( space * space ) > space ).       % Space.Restriction
tff(raff_type,  type, raff:  ( space * space ) > space ).       % Space.Raffination

% den: `(and (m_x p) (exists ((r Path)) (and (m_y r) (isPrefix r p))))`
tff(restr_def, axiom,
    ! [P: path, X: space, Y: space] :
      ( mem(P, restr(X,Y))
    <=> ( mem(P,X) & ? [R: path] : ( mem(R,Y) & isPrefix(R,P) ) ) ) ).

% eval: `case Space.Raffination(x_e, y_e) => recs(Subtraction(x_e, Restriction(x_e, y_e)))`
tff(raff_def, axiom,
    ! [X: space, Y: space] : raff(X,Y) = sdiff(X, restr(X,Y)) ).
