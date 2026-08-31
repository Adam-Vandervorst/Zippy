% ===========================================================================
% TIER 3 / iteration / tails-union.
%
% ITERATION WITH THE IDENTITY BODY IS TAILS-UNION.  docs/ALGEBRA.md defines
% `TailsUnion` by exactly this rewrite — group by head, ignore the head, emit the
% rest space — and the Scala side implements it as a `subs` rule.  Here it is a
% theorem for EVERY body F that behaves as the identity on the rest-space, which
% also certifies the rewrite in the direction the optimiser fires it (a
% tails-union may be re-expressed as an iteration, and back).
%
% GENERALISES: ALGEBRA.md's TailsUnion_Iteration rewrite (`Iteration(src,
% PathRef("_"), name, Mention(name))`)
%
% VERDICT: PROVED by vampire in 0.2s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_tails_ops.p').
include('_iter_ops.p').

tff(iteration_tailsunion, conjecture,
    ! [A: space, F: bodyF] :
      ( ( ! [H: item, S: space] : ap2(F,H,S) = S => iter(A,F) = tu(A) ) ) ).
