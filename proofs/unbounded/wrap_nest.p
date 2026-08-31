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
% THIS FILE: THE TWO NESTING ORDERS, which are the ones that must not be
% confused.  See the header above for why the orders differ.
%
% VERDICT: PROVED by vampire in 6.2s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').

tff(wrap_nest, conjecture,
    ! [A: space, U: path, V: path] :
      ( wrap(wrap(A,U),V) = wrap(A, app(V,U))
      & unwrap(unwrap(A,U),V) = unwrap(A, app(U,V)) ) ).
