% ===========================================================================
% NEGATIVE CONTROL / range.  `rng(A,Lo,Hi) = A` — a window is NOT the identity.
%
% WHAT THIS FILE USED TO SAY, AND WHY IT WAS WRONG.  It stated
%
%     ! [A,B,Lo,Hi] : ( sub(A,B) => sub(rng(A,Lo,Hi), rng(B,Lo,Hi)) )
%
% and expected NOT-PROVED, on the ground that a positional window is not
% monotone: adding a path to the source shifts every later RANK, so a bigger
% source can give a smaller window.  That is true of `Space.Range`.  It is NOT
% true of the statement above under `_range_ops.p`'s encoding, and vampire
% proves it in seconds:
%
%     P in rng(A,Lo,Hi)  ==>  mem(P,A)  (rng_sub)  and  ~plt(P,Lo) & plt(P,Hi)
%                             (rng_bounds);  A <= B gives mem(P,B);  rng_full
%                             then puts P in rng(B,Lo,Hi).
%
% THE ENDPOINTS IN THIS MODULE ARE PATHS, NOT RANKS — deliberately, because
% naming them by rank needs counting the module avoids — and with the endpoints
% FIXED the window is a pointwise order-interval filter, which IS monotone.  So
% the module cannot express the non-monotonicity of the real operator at all,
% and the previous file's own header conceded half of this ("only UNPROVABLE
% rather than refutable") while still claiming the control "pins that the corpus
% does not derive monotonicity".  The corpus DOES derive it, for fixed
% endpoints, so the control pinned nothing.
%
% WHERE THE REAL FACT LIVES.  Non-monotonicity of `Space.Range` is a property of
% `RangeBounds.normalize`'s RANK arithmetic — integer bounds against |x| — which
% is tier-1/tier-2's subject (`SpatialTypeSystem.windowWidth`), not this tier's.
% `COUNTERMODELS.tsv` carries the executed witness (A={m} <= B={a,m} with
% integer bounds 1..2), and that is an EXECUTOR fact, not a prover verdict.
% `docs/TRUSTED.md` T5 says so now.
%
% WHAT THIS CONTROL PINS INSTEAD, and it is genuinely unprovable here: a window
% is not the identity.  `rng_sub` gives one inclusion; the converse needs every
% path of `A` to lie in [Lo,Hi), which no axiom supplies for arbitrary
% endpoints.  This is the near-miss of `range_window.p`'s U61 ("a FULL window is
% the identity"), whose hypothesis is exactly what is dropped here — so if the
% corpus ever proved this, U61's full-window hypothesis would be vacuous and the
% operator would have been axiomatised as a no-op.
%
% Expected: NOT-PROVED.
% ===========================================================================
include('../_signature.p').
include('../_paths.p').
include('../_range_ops.p').
tff(not_range_identity, conjecture,
    ! [A: space, Lo: path, Hi: path] : ( rng(A,Lo,Hi) = A ) ).
