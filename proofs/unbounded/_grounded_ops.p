% =============================================================================
% TIER 3 operator module: GROUNDED (escapes to arbitrary Scala).  Include after
% `_signature.p`.
%
%   GroundedPS(p, f: PathValue => SpaceValue)
%   GroundedSS(s, f: SpaceValue => SpaceValue)
%
% THESE HAVE NO ALGEBRAIC LAWS, AND THAT IS THE POINT OF THIS FILE.  `f` is an
% arbitrary Scala function; nothing about it is knowable, so no law of the shape
% "grounded commutes with ..." or "grounded is monotone" can be stated, let alone
% proved.  `src/test/scala/UnboundedTier.scala` used to OMIT both constructors
% from its coverage map, which made a program containing one print a table with
% no row for it — indistinguishable from a program with no unsupported node.
%
% WHAT IS SUPPORTED IS ONE CONTRACT, AND IT IS LOAD-BEARING:
%
%   FUNCTIONALITY (DETERMINISM).  Equal inputs give equal outputs.  Every backend
%   assumes this the moment it SHARES or CACHES a grounded node — `transpile`
%   hash-conses the op-graph, `Interner` shares literals, the e-graph merges
%   equal terms, and the cost model prices a shared node once.  A grounded
%   function that consulted a clock or a mutable cell would break all four, and
%   nothing in the type would say so.  `grounded_functional.p` is that contract,
%   stated where a reader looking for the grounded laws will find it.
%
%   MONOTONICITY IS *NOT* ASSUMED, and `negative/not_grounded_monotone.p` is the
%   negative control that keeps it that way.  This is why
%   `AgnosticPipeline.monotoneInMention` returns false for a recursion variable
%   under a grounded node, and why `MORKL.mono`/`monoIn` forbid an SCC call
%   there: without monotonicity the least-post-fixpoint reading of an enclosing
%   `Fixpoint` is not available at all.
%
% CONSEQUENCE FOR THE SUPPORTED-TRANSLATION SURFACE.  A program containing a
% grounded node is supported for EXECUTION and for the pointwise/instance
% obligations (the node becomes an uninterpreted predicate, shared across both
% sides of an obligation — `EquivPipeline.AgSmt.denRaw`'s `Range`/grounded arm),
% and it is OUTSIDE the schematic tier: no operator law applies to it.
% REGISTRY.tsv row U71 records that boundary explicitly.
% =============================================================================

tff(gfun_type, type, gfun: $tType ).                     % an opaque Scala function
tff(gss_type,  type, gss:  ( gfun * space ) > space ).   % GroundedSS
tff(gps_type,  type, gps:  ( gfun * path )  > space ).   % GroundedPS

% THE CONTRACT.  In FOL this is a consequence of `gss`/`gps` being FUNCTION
% SYMBOLS, which is exactly the modelling decision being certified: it says the
% encoding of a grounded node as an applied function symbol is the right one,
% and it is what licenses sharing the node between the two sides of an
% obligation.  Stated explicitly so the corpus records the assumption a reader
% would otherwise have to infer from the signature.
tff(gss_functional, axiom,
    ! [F: gfun, S1: space, S2: space] : ( S1 = S2 => gss(F,S1) = gss(F,S2) ) ).
tff(gps_functional, axiom,
    ! [F: gfun, P: path, Q: path] : ( P = Q => gps(F,P) = gps(F,Q) ) ).
