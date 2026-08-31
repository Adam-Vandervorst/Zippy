% =============================================================================
% TIER 3 module: PATHS AS A FREE MONOID.  Include after `_signature.p` (which
% declares the `item` and `path` sorts).  These are exactly the append /
% isPrefix axioms `EquivPipeline.foPrelude` hands z3 and vampire for the
% instance tier, plus the term-algebra freeness facts that `declare-datatypes`
% gives z3 for free and a TPTP prover does not.
%
% KEPT OUT OF THE CORE.  Every included clause is a clause the saturation loop
% must consider.  MEASURED: a pure union/intersection goal that mentions no path
% structure at all is closed in 0.03 s from the set fragment alone and TIMES OUT
% at 120 s in portfolio mode once these ten monoid/prefix axioms are in scope.
% A theorem file therefore includes this module only if its statement mentions
% cons, app or isPrefix.  (`_appsplit.p` and `_prefix.p` are split off this
% module for the same reason and are included only where they are used.)
% =============================================================================

tff(nil_type,  type, nil:  path ).
tff(cons_type, type, cons: ( item * path ) > path ).
tff(app_type,  type, app:  ( path * path ) > path ).
tff(pfx_type,  type, isPrefix: ( path * path ) > $o ).

% append: the two defining equations of EquivPipeline.foPrelude
tff(app_nil_l, axiom, ! [Q: path] : app(nil, Q) = Q ).
tff(app_cons,  axiom,
    ! [H: item, T: path, Q: path] : app(cons(H,T), Q) = cons(H, app(T,Q)) ).

% certified lemma proofs/lemma_append_nil.smt2 (PROVED): append-nil on the right
tff(app_nil_r, axiom, ! [Q: path] : app(Q, nil) = Q ).

% associativity of append (proofs/laws/law_append_assoc.smt2 — the path-constant
% folding law; here it is the monoid axiom the operator theorems consume).
tff(app_assoc, axiom,
    ! [P: path, Q: path, R: path] : app(app(P,Q), R) = app(P, app(Q,R)) ).

% freeness of the term algebra: what `declare-datatypes` gives z3 for free.
tff(cons_not_nil, axiom, ! [H: item, T: path] : cons(H,T) != nil ).
tff(cons_inj, axiom,
    ! [H1: item, T1: path, H2: item, T2: path] :
      ( cons(H1,T1) = cons(H2,T2) => ( H1 = H2 & T1 = T2 ) ) ).
tff(path_cases, axiom,
    ! [P: path] : ( P = nil | ? [H: item, T: path] : P = cons(H,T) ) ).
