% ===========================================================================
% TIER 3 / grounded.  THE ONLY CONTRACT A GROUNDED NODE CARRIES: FUNCTIONALITY.
%
%   S1 = S2 => gss(F,S1) = gss(F,S2)        P = Q => gps(F,P) = gps(F,Q)
%
% `f` is an arbitrary Scala function, so no algebraic law about it can be stated.
% Determinism can, and it is load-bearing: `transpile` hash-conses the op-graph,
% `Interner` shares literals, the e-graph merges equal terms and the cost model
% prices a shared node ONCE — all four are wrong for a grounded function that
% consults a clock or a mutable cell, and nothing in the Scala type says so.
%
% WHY IT IS A CONJECTURE AND NOT JUST THE SIGNATURE.  In FOL it follows from
% `gss`/`gps` being function symbols, and that IS the modelling decision being
% certified: encoding a grounded node as an applied function symbol is what
% licenses sharing one uninterpreted predicate between the two sides of an
% instance obligation (`EquivPipeline.AgSmt.denRaw`'s grounded arm).  The file
% records the assumption where a reader looking for the grounded laws will find
% it, and `negative/not_grounded_monotone.p` records what may NOT be assumed.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_grounded_ops.p').
tff(grounded_functional, conjecture,
    ! [F: gfun, S1: space, S2: space, P: path, Q: path] :
      ( ( S1 = S2 => gss(F,S1) = gss(F,S2) )
      & ( P = Q  => gps(F,P)  = gps(F,Q)  ) ) ).
