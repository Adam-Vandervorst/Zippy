% =============================================================================
% General (unbounded, symbolic-graph) proof that R"transitive"'s doubling
% recursion denotes the same relation as the textbook one-hop transitive
% closure, for EVERY graph.
%
% path(X,Y)  = least relation with: edge(X,Y) => path(X,Y)
%                                    edge(X,Z) & path(Z,Y) => path(X,Y)
% path2(X,Y) = least relation with: edge(X,Y) => path2(X,Y)
%                                    path2(X,Z) & path2(Z,Y) => path2(X,Y)
%              (this is exactly R"transitive"'s recursion: R(E) unrolls to
%              the least X with X = E \/ (X o X))
%
% A first attempt used Z3's CHC/Spacer engine (transitive_chc.smt2) - unsound
% for this kind of property: with `edge` left as a fully free relation and no
% seed facts, the trivial all-false model satisfies every Horn clause
% regardless of whether the intended property is true or false (confirmed by
% a sanity check where a deliberately FALSE claim also came back "sat").
% A second attempt (transitive_equiv.smt2) fixed that by stating the
% least-fixpoint minimality condition as an explicit first-order axiom
% schema, instantiated at the specific witnesses the proof needs - but Z3's
% heuristic E-matching failed to find the necessary nested-quantifier
% instantiations and returned a spurious countermodel (traced by hand: the
% model violates path's own transitivity, which axiom ax_path_min_transQ
% below is supposed to force - Z3 just never fired it).
%
% Vampire's superposition calculus does complete first-order proof search
% (no E-matching pattern-guessing), so the identical minimality-axiom
% encoding is handed to it unchanged below.
% =============================================================================

fof(path_base, axiom,
    ! [X,Y] : (edge(X,Y) => path(X,Y)) ).

fof(path_step, axiom,
    ! [X,Y,Z] : ((edge(X,Z) & path(Z,Y)) => path(X,Y)) ).

fof(path2_base, axiom,
    ! [X,Y] : (edge(X,Y) => path2(X,Y)) ).

fof(path2_step, axiom,
    ! [X,Y,Z] : ((path2(X,Z) & path2(Z,Y)) => path2(X,Y)) ).

% path's minimality instantiated at Q := path2: path2 already satisfies
% path's two closure conditions (path2_base is literally path's base
% condition with path2 substituted in; the step condition follows from
% path2_base + path2_step, see the note in transitive_equiv.smt2), so path
% must be contained in path2.
fof(path_min_at_path2, axiom,
    ( ( ! [X,Y] : (edge(X,Y) => path2(X,Y)) )
    & ( ! [X,Y,Z] : ((edge(X,Z) & path2(Z,Y)) => path2(X,Y)) ) )
    => ! [X,Y] : (path(X,Y) => path2(X,Y)) ).

% path's minimality instantiated at Q(X,Y) := (! [C] : path(Y,C) => path(X,C))
% ("everything reachable from Y is reachable from X"). Closure under edge
% follows directly from path_step; the conclusion is exactly path's own
% transitivity, which is NOT one of path's two defining axioms - it's an
% inductive consequence of them, and this is the derivation that
% establishes it.
fof(path_min_at_transQ, axiom,
    ( ( ! [X,Y] : (edge(X,Y) => ! [C] : (path(Y,C) => path(X,C))) )
    & ( ! [X,Y,W] : ((edge(X,W) & (! [C] : (path(Y,C) => path(W,C))))
                      => (! [C] : (path(Y,C) => path(X,C)))) ) )
    => ! [X,Y] : (path(X,Y) => (! [C] : (path(Y,C) => path(X,C)))) ).

% path2's minimality instantiated at Q := path: path satisfies path2's two
% closure conditions (base: path2_base's condition with path substituted in,
% which is path_base itself; step: path's own transitivity, established by
% path_min_at_transQ above), so path2 must be contained in path.
fof(path2_min_at_path, axiom,
    ( ( ! [X,Y] : (edge(X,Y) => path(X,Y)) )
    & ( ! [X,Y,Z] : ((path(X,Z) & path(Z,Y)) => path(X,Y)) ) )
    => ! [X,Y] : (path2(X,Y) => path(X,Y)) ).

fof(transitive_equals_path2, conjecture,
    ! [X,Y] : (path(X,Y) <=> path2(X,Y)) ).
