% ===========================================================================
% TIER 3 / restriction / raffination.
%
% PREFIX-DISJOINTNESS IMPLIES EMPTINESS.  If no path of Y is a prefix of any
% path of X then the restriction is EMPTY, the raffination is all of X, and X and
% Y are themselves disjoint (because `isPrefix` is reflexive).  This is the law
% behind the trie shortcut that skips an entire subtrie on a prefix mismatch: the
% implementation decides it structurally per node, and here it is decided once,
% for all X and Y.
%
% GENERALISES: the disjoint-prefix shortcut in the trie backends
% (docs/guide.md: 'a trie intersection can ignore entire subtries based on a
% disjoint prefix')
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_prefix.p').
include('_prefix_ops.p').

tff(prefix_disjoint, conjecture,
    ! [X: space, Y: space] :
      ( ( ! [P: path, R: path] : ( ( mem(P,X) & mem(R,Y) ) => ~ isPrefix(R,P) )
      => ( restr(X,Y) = empty & raff(X,Y) = X & disj(X,Y) ) ) ) ).
