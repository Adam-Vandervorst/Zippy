% ===========================================================================
% TIER 3 / call + fixpoint.  THE `Fix` NODE IS BELOW EVERY SOLUTION of the
% union-saturating recursion it replaced.
%
%   S = union(I, ap1(G,S))   =>   sub(fix(I,G), S)
%
% Half of the theorem `asFixpoint` (MORKL.scala) and `asFixpointGeneral` need:
% they REWRITE a recursive routine `r(m) = m u r(T(m))` into `Space.Fixpoint`,
% and what licenses that is that the `Fixpoint` node denotes the LEAST solution
% of the recursion.  The other half — that it IS a solution — is
% `call_fix_solves.p`.  `terminating/asfixpoint_sound.smt2` (O2) makes the same
% claim for one concrete recurrence over a finite universe.
%
% NO MONOTONICITY HYPOTHESIS IS NEEDED HERE: a solution is in particular a
% post-fixpoint above `I`, and `fix_least` applies directly.
%
% SPLIT FROM THE OTHER HALF ON PURPOSE.  Stated as one conjunction with the
% nested `ForAll S` inside, vampire did not close it at a 120 s portfolio budget
% (measured 2026-09-02); each half alone is immediate.  Same discipline as
% `iteration_split_sub`/`_sup` and the `kleene_*_base`/`_step` pairs.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_fix_ops.p').
include('_call_ops.p').
tff(call_fix_least, conjecture,
    ! [I: space, G: bodyG, S: space] :
      ( satSol(I,G,S) => sub(fix(I,G), S) ) ).
