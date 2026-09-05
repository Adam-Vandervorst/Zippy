% ===========================================================================
% TIER 3 / call + fixpoint.  `fix(I,G)  SUBSET  union(I, ap1(G,fix(I,G)))` when
% the step is MONOTONE — the half of "the `Fix` node is a solution" where
% monotonicity is actually used.
%
% THE ARGUMENT, and why the candidate is NAMED.  Apply `fix_least` to
% `Y = union(I, ap1(G,fix(I,G)))`.  Its first premise `sub(I,Y)` is immediate;
% its second, `sub(ap1(G,Y), Y)`, follows from `Y subset fix(I,G)`
% (`call_fix_solves_sup.p`) by MONOTONICITY of `G` and then `fix_closed`.  That
% is the same place monotonicity earns its keep in
% `terminating/fixpoint_is_lfp.smt2` (O1) — leastness, not termination.
%
% MEASURED 2026-09-02: with `Y` written out inline, vampire did not close this
% at a 150 s portfolio budget — `fix_least` has to be instantiated at a compound
% term nothing in the goal builds.  Naming it with `cand` puts the term in the
% signature and the proof is found at once.  Same reason `fixpoint_is_lfp.smt2`
% asserts its four set-algebra stepping stones instead of letting z3 look for
% the extensionality instances.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_fix_ops.p').
include('_call_ops.p').
tff(cand_type, type, cand: ( space * bodyG ) > space ).
tff(cand_def, axiom,
    ! [I: space, G: bodyG] : cand(I,G) = cup(I, ap1(G, fix(I,G))) ).
tff(call_fix_solves_sub, conjecture,
    ! [I: space, G: bodyG] :
      ( monoG(G) => sub(fix(I,G), cand(I,G)) ) ).
