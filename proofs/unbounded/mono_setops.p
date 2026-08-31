% ===========================================================================
% TIER 3 / union / intersection / subtraction.
%
% MONOTONICITY of the three set operators in each argument.  Note the mixed
% variance of subtraction — monotone in the minuend, ANTITONE in the subtrahend —
% which is exactly the direction the tier-1 Subtraction transfer encodes with
% `lo_a - hi_b` and which nothing in tier-1 or tier-2 states.
%
% GENERALISES: every `SC.reduce` rewrite that replaces a subterm by a
% smaller/larger one
%
% VERDICT: PROVED by vampire in 0.1s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').

tff(mono_setops, conjecture,
    ! [A: space, B: space, C: space, D: space] :
      ( ( ( sub(A,C) & sub(B,D) ) => sub(cup(A,B), cup(C,D)) )
      & ( ( sub(A,C) & sub(B,D) ) => sub(cap(A,B), cap(C,D)) )
      & ( ( sub(A,C) & sub(D,B) ) => sub(sdiff(A,B), sdiff(C,D)) ) ) ).
