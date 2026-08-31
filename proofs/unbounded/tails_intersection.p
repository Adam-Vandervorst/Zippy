% ===========================================================================
% TIER 3 / tails-intersection.
%
% TailsIntersection(s) = { t : s has AT LEAST ONE head, and for EVERY head h
% of s, h::t in s }.  The theorem records the three things that are easy to get
% wrong:
%   * it is contained in the tails-UNION (so it is never larger),
%   * BOTH degenerate sources give EMPTY — `ti({}) = {}` and `ti({eps}) = {}`.
%     Dropping the "at least one head" conjunct would make an unheaded source
%     yield EVERY tail, which is the `{}` vs `{eps}` confusion docs/traps.md 1
%     puts first,
%   * when the source has exactly ONE head the two tails operators coincide.
% The single-head case is the one the trie backend specialises, and this is the
% schematic statement of when that specialisation is sound.
%
% GENERALISES: proofs/threeway_tailsinter_trie.smt2 and
% proofs/keyfold_tailsinter.smt2 (instance tier)
%
% VERDICT: PROVED by vampire in 0.2s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_tails_ops.p').

tff(tails_intersection, conjecture,
    ! [A: space] :
      ( sub(ti(A), tu(A))
      & ti(empty) = empty
      & ti(sing(nil)) = empty
      & ( ! [H: item, K: item] : ( ( headed(H,A) & headed(K,A) ) => H = K )
          => ti(A) = tu(A) ) ) ).
