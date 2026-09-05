% ===========================================================================
% TIER 3 / composition.
%
% Composition distributes over union in BOTH arguments and is monotone in
% both.  This is what licenses hoisting a union out of either side of a product —
% the rewrite family docs/guide.md asks to be preferred over per-program
% specialisation.
%
% GENERALISES: the union-hoisting rewrites in SC.reduce / formal.egg
%
% THIS FILE: THE TWO DISTRIBUTIVITY LAWS ONLY.  Monotonicity of `comp` in both
% arguments moved to `mono_concat.p`, where the rest of the concatenation
% monotonicity table lives; keeping three conjuncts here timed out at 60 s while
% the two distributivity laws alone are fast.
%
% VERDICT: PROVED by vampire in 5.6s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').

tff(composition_distrib, conjecture,
    ! [A: space, B: space, C: space] :
      ( comp(cup(A,B), C) = cup(comp(A,C), comp(B,C))
      & comp(A, cup(B,C)) = cup(comp(A,B), comp(A,C)) ) ).
