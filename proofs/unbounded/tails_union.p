% ===========================================================================
% TIER 3 / tails-union.
%
% TailsUnion(s) = { t : SOME h with h::t in s }.  It is a UNION
% homomorphism (a head group contributes independently), it is monotone, and it is
% only SUB-multiplicative on intersections: a tail can appear under two different
% heads on the two sides, so `tu(A n B)` is contained in `cap(tu A, tu B)` and NOT
% equal to it.  Stating the containment rather than an equation is the point —
% the equation is false, and the corpus does not pretend otherwise.
% Both empty corners are here: `tu({}) = {}` and `tu({eps}) = {}` (an
% empty path has no head, so it contributes nothing — docs/traps.md 1).
%
% GENERALISES: proofs/threeway_tailsunion_trie.smt2 (instance tier),
% tier-1's TailsUnion arm (`hi = hi_src`)
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_tails_ops.p').

tff(tails_union, conjecture,
    ! [A: space, B: space, C: space] :
      ( tu(empty) = empty
      & tu(sing(nil)) = empty
      & tu(cup(A,B)) = cup(tu(A), tu(B))
      & sub(tu(cap(A,B)), cap(tu(A), tu(B)))
      & ( sub(A,B) => sub(tu(A), tu(B)) ) ) ).
