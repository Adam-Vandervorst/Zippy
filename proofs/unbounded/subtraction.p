% ===========================================================================
% TIER 3 / subtraction.
%
% The subtraction facts the size analysis's Subtraction transfer silently
% assumes: the result is inside the minuend, disjoint from the subtrahend, and
% splits the minuend together with the meet.  docs/traps.md 1 records that
% `a \ b == b` is never an identity case in the trie fast paths — the
% `sdiff(A,B) = sdiff(A, cap(A,B))` conjunct is the schematic form of why.
%
% GENERALISES: tier-1 Lower.sizeBounds Subtraction arm (`lo = max(0, lo_a -
% hi_b)`, `hi = hi_a`)
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').

tff(subtraction, conjecture,
    ! [A: space, B: space, C: space] :
      ( sub(sdiff(A,B), A)
      & disj(sdiff(A,B), B)
      & cup(cap(A,B), sdiff(A,B)) = A
      & sdiff(A,A) = empty
      & sdiff(A, empty) = A
      & sdiff(A,B) = sdiff(A, cap(A,B)) ) ).
