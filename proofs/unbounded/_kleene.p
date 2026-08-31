% =============================================================================
% TIER 3 module: THE KLEENE CHAIN THAT `eval` ACTUALLY RUNS.  Include after
% `_signature.p` and `_fix_ops.p`.
%
% src/main/scala/MORKL.scala, `case Space.Fixpoint(init, rec, body)`:
%
%     var cur = recs(init); var acc = cur
%     while !stop do
%       val nxt = eval(body)(rec -> cur)
%       if nxt == cur then stop = true else { acc = acc union nxt; cur = nxt }
%     acc
%
% so there are TWO sequences, not one, and modelling only the accumulator would
% quietly change the program:
%
%   cur(0) = init,        cur(n+1) = body[cur(n)]        -- the iterate
%   acc(0) = init,        acc(n+1) = acc(n) u cur(n+1)   -- the returned value
%
% (docs/SUPERCOMPILER.md's "init u body[init] u body^2[init] ..." is `acc`.)
% This is the same two-sequence shape terminating/reachable_value.p uses for
% R"reachable", down to the names `iter`/`acc`.
%
% THE INDEX SORT IS ABSTRACT.  `idx` with `z`/`s` — no `$int`, no arithmetic.
% See `_nat.p` for the measured reason built-in integers are banned from this
% corpus.  Since `idx` is an opaque sort rather than a term algebra, vampire has
% no structural-induction rule for it, so the induction is STAGED BY HAND: each
% Kleene theorem is split into a BASE file and a STEP file, both of which are
% ordinary induction-free first-order obligations, and the ForAll-n conclusion
% follows by induction on the recursion depth at the meta level.  This is the
% same staging terminating/no_infinite_descent.smt2 already uses ("unlike
% no_infinite_descent.smt2, where the induction had to be staged by hand" —
% terminating/reachable_value.p's header).  Nothing is assumed that the base and
% step files do not prove.
% =============================================================================

tff(idx_type, type, idx: $tType ).
tff(z_type,   type, z: idx ).
tff(s_type,   type, s: idx > idx ).

tff(i0_type,  type, i0: space ).            % the fixpoint's `init`
tff(g0_type,  type, g0: bodyG ).            % the fixpoint's `body`
tff(cur_type, type, cur: idx > space ).
tff(acc_type, type, acc: idx > space ).

tff(cur_base, axiom, cur(z) = i0 ).
tff(cur_step, axiom, ! [N: idx] : cur(s(N)) = ap1(g0, cur(N)) ).
tff(acc_base, axiom, acc(z) = i0 ).
tff(acc_step, axiom, ! [N: idx] : acc(s(N)) = cup(acc(N), cur(s(N))) ).
