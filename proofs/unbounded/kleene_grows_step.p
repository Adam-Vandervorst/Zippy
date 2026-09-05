% ===========================================================================
% TIER 3 / fixpoint.  THE ACCUMULATOR CONTAINS THE SEED — STEP CASE.
%
% `acc(N+1) = acc(N) u cur(N+1)` is a union with `acc(N)`, so anything already
% in `acc(N)` survives.  No hypothesis on the body at all — the accumulation
% alone carries the seed forward, which is the point: a fixpoint loop that
% overwrote its accumulator (`cur := body(cur)` only) would lose it.
%
% With `kleene_grows_base.p` this gives `ForAll N: sub(init, acc(N))` by
% induction on the recursion depth, which is the premise `kleene_conv.p` needs
% in order to apply `fix_least` at `X := acc(k)`.
%
% GENERALISES: the same tier-2 closure edge as the base case, for all depths.
%
% VERDICT: PROVED by vampire in 0.1s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_fix_ops.p').
include('_kleene.p').

tff(kleene_grows_step, conjecture,
    ! [N: idx] : ( sub(i0, acc(N)) => sub(i0, acc(s(N))) ) ).
