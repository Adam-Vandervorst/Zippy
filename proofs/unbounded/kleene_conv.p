% ===========================================================================
% TIER 3 / fixpoint.  AT ITS CONVERGENCE DEPTH, EVAL'S LOOP IS THE LEAST
% PRE-FIXPOINT.
%
%     cur(k+1) = cur(k)   =>   acc(k) = fix(init, body)
%
% This is the theorem that ties `eval`'s `while` loop — which stops the first
% time a round changes nothing (`if nxt == cur then stop = true`) — to the Park
% characterisation `_fix_ops.p` axiomatises.  Without it, tier 3's `fix` and the
% executors' fixpoint are two unrelated objects that happen to share a name, and
% every fixpoint theorem in this corpus would be about something the code does
% not compute.
%
% STAGED, NOT INDUCTIVE.  The three inductions live in six separate files and
% their ForAll-n conclusions are IMPORTED HERE AS PREMISES — the same staging
% discipline terminating/reachable_value.p uses for `step_in_mask` and
% terminating/scc_decrease.p for its `pred_*` / `desc_*` facts:
%
%   kleene_below   (kleene_below_base.p + kleene_below_step.p)
%                  every iterate and every accumulation lies below every
%                  pre-fixpoint.  At X := fix(i0,g0) it gives sub(acc(k), fix).
%   kleene_grows   (kleene_grows_base.p + kleene_grows_step.p)
%                  every accumulation contains the seed — needed to apply
%                  `fix_least` at X := acc(k).
%   acc_is_cur     (kleene_acc_is_cur_base.p + kleene_acc_is_cur_step.p)
%                  under an EXTENSIVE body the accumulation and the last iterate
%                  coincide — this is what lets the loop's stopping test, which
%                  is a test on the ITERATE (`nxt == cur`), be read as a
%                  statement about the value the loop RETURNS.
%
% Given those, the argument is short and induction-free: `converged` turns
% `cur(s(k)) = ap1(g0, cur(k))` into `ap1(g0, acc(k)) = acc(k)`, so `acc(k)` is a
% pre-fixpoint above the seed; `fix_least` gives `sub(fix, acc(k))`;
% `kleene_below` gives the reverse; antisymmetry closes it.  If this file ever
% needed an induction flag, a premise would be missing.
%
% THE HYPOTHESES ARE THE HONEST ONES.  `monoG` and extensivity are both stated,
% neither is assumed globally, and both are exactly what the union-saturating
% shape `Union(Mention(rec), f)` that `asFixpoint` recognises provides.  For a
% body outside that shape the theorem is simply not claimed.
%
% GENERALISES: terminating/least_fixpoint_unique.p, which shows that whichever
% least solution you construct is unique but says nothing about the loop that
% constructs it; and the executors' `nxt == cur` stopping rule, which is
% asserted by construction and nowhere certified.
%
% VERDICT: PROVED by vampire in 2.4s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_lattice_lemmas.p').
include('_fix_ops.p').
include('_kleene.p').

tff(k_type, type, k: idx ).

% --- the body is monotone and extensive: the union-saturating shape
tff(mono_body,      axiom, monoG(g0) ).
tff(extensive_body, axiom, ! [S: space] : sub(S, ap1(g0,S)) ).

% --- staged lemmas, each PROVED as a base/step pair in its own file
tff(kleene_below, axiom,
    ! [N: idx, X: space] :
      ( ( sub(i0,X) & sub(ap1(g0,X), X) ) => ( sub(cur(N),X) & sub(acc(N),X) ) ) ).
tff(kleene_grows, axiom, ! [N: idx] : sub(i0, acc(N)) ).
tff(acc_is_cur,   axiom, ! [N: idx] : acc(N) = cur(N) ).

% --- the loop's own stopping test: the round at depth k changed nothing
tff(converged, axiom, cur(s(k)) = cur(k) ).

tff(kleene_conv, conjecture, acc(k) = fix(i0, g0) ).
