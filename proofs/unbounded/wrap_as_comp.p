% ===========================================================================
% TIER 3 / wrap / unwrap / composition.
%
% WRAP AND UNWRAP NEST IN OPPOSITE ORDERS.  wrap prepends, so nesting
% composes the prefixes RIGHT-to-left (`wrap(wrap(A,U),V) = wrap(A, app(V,U))`);
% unwrap strips from the front, so nesting composes them LEFT-to-right
% (`unwrap(unwrap(A,U),V) = unwrap(A, app(U,V))`).  Reversing either is a silent
% wrong answer and is precisely the bug docs/traps.md 4 records for
% `UnwrapConcat_Unwraps`.  The first conjunct pins wrap to composition with a
% singleton, which is how `eval` actually implements it.
%
% GENERALISES: UnwrapConcat_Unwraps — the law docs/traps.md 4 records as
% having stripped Concat-prefix factors in REVERSED order
%
% THIS FILE: `wrap(A,W) = comp(sing(W), A)` — the identity `eval` implements
% literally (`case Space.Wrap(src_e, p_e) => recs(Composition(Singleton(p_e),
% src_e))`).  Split from the nesting laws because the conjunction of the three
% timed out at 60 s and each is fast alone.
%
% VERDICT: PROVED by vampire in 0.3s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').

tff(wrap_as_comp, conjecture,
    ! [A: space, W: path] :
      ( wrap(A,W) = comp(sing(W), A) ) ).
