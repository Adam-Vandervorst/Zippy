% =============================================================================
% TIER 3 — THE UNBOUNDED TIER.  Core signature for proofs/unbounded/*.p.
%
% WHY THIS TIER EXISTS.  The repository already reasons about sizes and lengths
% at two tiers, both of which are BOUNDED to one concrete term:
%
%   tier-1  Lower.sizeBounds / Lower.lenBounds  (src/main/scala/MORKL.scala) —
%           a syntactic interval propagation.  It computes an interval FOR A
%           GIVEN AST.  There is no object language in which "for all spaces A
%           and B, |A u B| =< |A| + |B|" can even be written down: the transfer
%           function for Union IS that fact, hard-coded in Scala, and the only
%           way it is checked is empirically, by the corpus differential gate.
%
%   tier-2  SizeZ3 / LenZ3  (src/main/scala/SizeConstraints.scala,
%           src/main/scala/LengthConstraints.scala) — a GROUND SMT encoding.
%           `encode` walks the hash-consed AST and emits, LITERALLY,
%           `(declare-const n<i> Int)` and `(declare-const e<i> Int)` per node
%           (SizeConstraints.scala:196-202), then one linear constraint per
%           constructor occurrence and `(minimize n<root>)` / `(maximize
%           n<root>)`.  The problem handed to z3 is quantifier-free linear
%           integer arithmetic over a FIXED, FINITE set of node variables.  It
%           is strictly more precise than tier-1 (it sees the saturated subset
%           relation) and exactly as bounded: change the term and you get a
%           different, unrelated constraint system.  Nothing in it ranges over
%           "all spaces", "all paths", or "all n".
%
%   NEITHER TIER CAN STATE A SCHEMATIC CLAIM.  A schematic claim quantifies over
%   the INPUTS (all spaces A, B) and over UNBOUNDED DATA (all paths, all
%   recursion depths n).  Tier-1 has no quantifiers at all; tier-2 has a finite
%   supply of ground integer constants, one per node of one term.  Both are
%   therefore INSTANCE reasoning: they certify a bound for the term in hand.
%   Tier 3 is the missing tier — the operator laws themselves, quantified over
%   all inputs, in first-order logic, discharged by vampire.
%
% ENCODING DECISIONS, AND WHY.
%
%   (1) SPACES ARE A SORT, NOT UNARY PREDICATES.  The SMT prelude in
%       src/main/scala/EquivPipeline.scala compiles each space to a
%       `(define-fun m_k ((p Path)) Bool ...)` — a unary predicate.  That is
%       right for tier-2-style INSTANCE proofs (two given programs, one goal),
%       but it cannot carry this tier's whole point: FOL has no quantifier over
%       predicates, so "for all spaces A, B: ..." would degenerate into a
%       metalevel schema with one .p file per instantiation — exactly the
%       bounded reasoning we are trying to escape.  We therefore REIFY spaces
%       into the sort `space`, with `mem : path * space > $o` as membership and
%       EXTENSIONALITY as an axiom.  Every operator axiom (in the `_*_ops.p`
%       modules) is the literal transcription of the corresponding arm of
%       `EquivPipeline.Smt.den` — itself the transcription of the arm of `eval`
%       in src/main/scala/MORKL.scala — with `(m_k p)` replaced by `mem(P, A)`.
%
%   (2) BODIES ARE REIFIED TOO.  `Iteration` and `Fixpoint` are second-order in
%       Scala: their body is a term with a free binder.  For the same reason as
%       (1) they get sorts `bodyF` in `_iter_ops.p` and `bodyG` in `_fix_ops.p`.
%
%   (3) PATHS ARE A FREE MONOID (module `_paths.p`), with exactly the axioms
%       `EquivPipeline.foPrelude` already uses, PLUS the two certified lemmas
%       proofs/lemma_append_nil.smt2 and proofs/lemma_append_cons.smt2 (both
%       PROVED — see proofs/STATUS.tsv), so tier 3 rests on the same append
%       theory as the instance tier.  The freeness axioms (cons injective,
%       cons =/= nil, exhaustive cases) are what `declare-datatypes` gives z3 for
%       free and vampire does not.
%
% WHY THE SIGNATURE IS SPLIT INTO MODULES.  Everything a theorem file includes
% is a clause the saturation loop must consider, and the cost is not marginal.
% TWO MEASUREMENTS DROVE THE SPLIT:
%
%   * A 22-conjunct union/intersection lattice goal that mentions no path
%     structure at all is closed in 0.03 s from the set fragment alone, TIMES
%     OUT at 120 s once the ten free-monoid/prefix axioms are also in scope, and
%     times out again at 120 s with the full operator table.  Same goal, same
%     prover, same flags.  (That goal is now the six files `lattice_union.p`,
%     `lattice_inter.p`, `lattice_distrib.p`, `lattice_order.p`,
%     `subtraction.p`, `mono_setops.p`, each of which closes in under 0.3 s —
%     splitting the CONJUNCTION mattered as much as splitting the signature,
%     because a conjunctive goal is a disjunction after negation.)
%
%   * Adding the integer-valued `plen` axioms to that same overloaded signature
%     made vampire 5.1.0's ALASCA/ARI schedule answer `SZS status
%     ContradictoryAxioms` for the lattice goal — a SPURIOUS inconsistency
%     derived from the BUILT-IN integer theory axioms alone (the printed
%     derivation ends with `equality_resolution` turning
%     `$sum(X0,X1) != X1 | 2 != X0` into `2 != X0`, which does not follow).  An
%     inconsistent axiom set proves every conjecture, so this is exactly the
%     "an encoding that proves everything proves nothing" failure mode.
%
% The corpus is therefore modular: each theorem file includes this core plus
% ONLY the modules its statement mentions, and `run.sh` treats
% `ContradictoryAxioms` as a HARD FAILURE, never as a proof.
%
% THE MODULES.  Definitional (transcribed from `eval` / `den`):
%
%   _signature.p      sorts, spaces, u / n / \, sub, disj, sing   (this file)
%   _paths.p          paths as a free monoid
%   _prefix.p         the isPrefix relation
%   _appsplit.p       the certified append-cons split lemma
%   _prefix_ops.p     Restriction, Raffination
%   _concat_ops.p     Composition, Wrap, Unwrap
%   _tails_ops.p      TailsUnion, TailsIntersection, head groups
%   _iter_ops.p       Iteration (reified body sort `bodyF`)
%   _fix_ops.p        Fixpoint (reified body sort `bodyG`, Park characterisation)
%   _kleene.p         the two-sequence Kleene chain `eval`'s loop actually runs
%
% Measure-theoretic (all over the uninterpreted ordered monoid `num` — this
% corpus contains NO built-in arithmetic, see `_nat.p` for the measured reason):
%
%   _nat.p            (num, plus, zero, le): an ordered commutative monoid
%   _plen.p           path length
%   _lenbounds.p      the lenLB / lenUB predicates
%   _card.p           cardinality
%   _card_image.p     the injective-image counting principle
%
% Staged lemmas — every formula in these is a conjunct of a conjecture PROVED
% elsewhere in this corpus, imported as a premise so a harder theorem does not
% re-derive it inside its own saturation (the discipline
% terminating/reachable_value.p uses for `step_in_mask`):
%
%   _lattice_lemmas.p from lattice_order/union/inter, subtraction, mono_setops
%   _partitions.p     from set_partitions.p
%   _grp_lemmas.p     from grp_union.p
%   _cancel.p         from mon_cancel_base.p + mon_cancel_step.p, with the
%                     induction principle itself unmechanised (mon_cancel.p is
%                     the direct attempt and is the corpus's one OPEN file)
%
% WHAT IS AN AXIOM HERE AND WHAT IS NOT.  Everything below is either
%   (a) a DEFINITION (an iff or an equation introducing a symbol, transcribed
%       from `eval`/`den` — definitional, hence conservative),
%   (b) EXTENSIONALITY, or
%   (c) a FREE-MONOID fact.
% No lattice law, no monotonicity fact, no cardinality fact is assumed: those
% are the conjectures of the theorem files.
% =============================================================================

% ---------------------------------------------------------------- sorts
tff(item_type,  type, item:  $tType ).      % path items (Scala: PathItem)
tff(path_type,  type, path:  $tType ).      % finite words over item (Scala: PathValue)
tff(space_type, type, space: $tType ).      % finite sets of paths (Scala: SpaceValue)

% ---------------------------------------------------------------- spaces
tff(mem_type,   type, mem:   ( path * space ) > $o ).
tff(sub_type,   type, sub:   ( space * space ) > $o ).
tff(disj_type,  type, disj:  ( space * space ) > $o ).
tff(empty_type, type, empty: space ).
tff(sing_type,  type, sing:  path > space ).

tff(extensionality, axiom,
    ! [A: space, B: space] :
      ( ( ! [P: path] : ( mem(P,A) <=> mem(P,B) ) ) => A = B ) ).

tff(sub_def,  axiom,
    ! [A: space, B: space] : ( sub(A,B) <=> ! [P: path] : ( mem(P,A) => mem(P,B) ) ) ).
tff(disj_def, axiom,
    ! [A: space, B: space] : ( disj(A,B) <=> ! [P: path] : ~ ( mem(P,A) & mem(P,B) ) ) ).

tff(empty_def, axiom, ! [P: path] : ~ mem(P, empty) ).
tff(sing_def,  axiom, ! [P: path, Q: path] : ( mem(P, sing(Q)) <=> P = Q ) ).

% ---------------------------------------------------------------- u / n / \
% eval: `recs(x) union recs(y)`  /  den: `(or (m_a p) (m_b p))`
tff(cup_type, type, cup: ( space * space ) > space ).           % Space.Union
tff(cup_def, axiom,
    ! [P: path, A: space, B: space] : ( mem(P, cup(A,B)) <=> ( mem(P,A) | mem(P,B) ) ) ).

% eval: `recs(x) intersect recs(y)`  /  den: `(and (m_a p) (m_b p))`
tff(cap_type, type, cap: ( space * space ) > space ).           % Space.Intersection
tff(cap_def, axiom,
    ! [P: path, A: space, B: space] : ( mem(P, cap(A,B)) <=> ( mem(P,A) & mem(P,B) ) ) ).

% eval: `recs(x) removedAll recs(y)`  /  den: `(and (m_a p) (not (m_b p)))`
tff(sdiff_type, type, sdiff: ( space * space ) > space ).       % Space.Subtraction
tff(sdiff_def, axiom,
    ! [P: path, A: space, B: space] : ( mem(P, sdiff(A,B)) <=> ( mem(P,A) & ~ mem(P,B) ) ) ).
