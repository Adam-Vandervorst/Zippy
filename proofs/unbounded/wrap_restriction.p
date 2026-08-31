% ===========================================================================
% TIER 3 / wrap / unwrap / restriction.
%
% THE OTHER ROUND TRIP: `wrap(unwrap(A,W),W) = restr(A, sing(W))`.  Unwrapping
% then re-wrapping does NOT recover A; it recovers exactly the part of A that lies
% under the prefix W.  docs/traps.md 4 records the historical bug here in as many
% words: "`SingletonRestriction_Unwrap` dropped the restriction prefix (must
% RE-WRAP)".  Stating it schematically is what makes the re-wrap non-optional.
% Note this direction needs NO cancellation — only `isPrefix_app`.
%
% GENERALISES: SingletonRestriction_Unwrap — the law docs/traps.md 4 records
% as having once DROPPED the restriction prefix
%
% VERDICT: PROVED by vampire in 0.2s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').
include('_prefix.p').
include('_prefix_ops.p').

tff(wrap_restriction, conjecture,
    ! [A: space, W: path] :
      ( wrap(unwrap(A,W),W) = restr(A, sing(W)) ) ).
