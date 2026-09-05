% ===========================================================================
% TIER 3 / unwrap.
%
% UNWRAP IS A BOOLEAN HOMOMORPHISM: it commutes with union, intersection AND
% subtraction, and it is monotone.  Wrap commutes with union only — it is
% injective but not surjective, so it does not commute with subtraction — so the
% two are deliberately stated apart.  The homomorphism property is what lets the
% optimiser push an unwrap through an arbitrary set-algebra subterm.
%
% GENERALISES: the `Unwrap` arms of SC.reduce and of tier-1 Lower.sizeBounds
% (`lo = 0`, `hi = hi_src`)
%
% VERDICT: PROVED by vampire in 0.7s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').

tff(unwrap_hom, conjecture,
    ! [A: space, B: space, W: path] :
      ( unwrap(cup(A,B),W) = cup(unwrap(A,W), unwrap(B,W))
      & unwrap(cap(A,B),W) = cap(unwrap(A,W), unwrap(B,W))
      & unwrap(sdiff(A,B),W) = sdiff(unwrap(A,W), unwrap(B,W))
      & unwrap(empty,W) = empty
      & ( sub(A,B) => sub(unwrap(A,W), unwrap(B,W)) ) ) ).
