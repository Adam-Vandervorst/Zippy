% ===========================================================================
% TIER 3 / fixpoint.  ACCUMULATOR = LAST ITERATE — STEP CASE.
%
%     body EXTENSIVE  &  acc(N) = cur(N)   =>   acc(N+1) = cur(N+1)
%
% because `acc(N+1) = acc(N) u cur(N+1) = cur(N) u body[cur(N)]`, and
% extensivity (`S <= body[S]` for every S) collapses that union to `body[cur(N)]
% = cur(N+1)`.
%
% EXTENSIVITY IS EXACTLY THE UNION-SATURATING SHAPE.  `lowerCalls`/`asFixpoint`
% only produces a `Space.Fixpoint` from a routine whose body is
% `Union(Mention(rec), f)` (docs/SUPERCOMPILER.md), and for such a body
% `body[S] = S u f[S] >= S`.  The hypothesis is stated rather than assumed
% because it is genuinely necessary: for a NON-extensive body the accumulation
% is strictly larger than the last iterate, and `eval`'s `nxt == cur` stopping
% test is then strictly weaker than "the returned value stopped growing".  That
% is the honest boundary of `kleene_conv.p`.
%
% GENERALISES: the `asFixpoint` recognition condition, which is enforced
% syntactically and nowhere certified semantically.
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_lattice_lemmas.p').
include('_fix_ops.p').
include('_kleene.p').

tff(kleene_acc_is_cur_step, conjecture,
    ! [N: idx] :
      ( ( ! [S: space] : sub(S, ap1(g0,S)) & acc(N) = cur(N) )
     => acc(s(N)) = cur(s(N)) ) ).
