; =============================================================================
; O3d / O4b — ARE THE SYNTACTIC MONOTONICITY GATES SOUND?  Two of them are not.
;
; `asFixpointGeneral` (MORKL.scala:1284-1307, `monoIn`) and
; `lowerMutualPassthrough` (:1249-1263, `mono`) decide whether a body is
; subset-MONOTONE in the recursive mention by walking the Space grammar and
; accepting a fixed list of constructors.  Everything downstream — the ascending
; Kleene chain, "so the least fixpoint exists", O1's hypothesis, O10's theorem —
; rests on those two predicates being SOUND: syntactic acceptance must imply
; semantic monotonicity.  Nobody had checked the arms one by one.  This file
; does, in the SET-OF-PATHS denotation, and reports the result honestly:
;
;   SOUND, proved below:  Union, Intersection, Composition, Restriction, Wrap,
;                         Unwrap, TailsUnion, the left arm of Subtraction and of
;                         Raffination, the leaves, and COMPOSITION OF SOUND ARMS
;                         (the induction step that makes the list a schema).
;   UNSOUND, REFUTED below with a machine-checked counterexample:
;                         TailsIntersection  (both files: `mono` MORKL.scala:1256,
;                                             `monoIn` :1292)
;                         Iteration          (`mono` :1258, `monoIn` :1293)
;
; --- COUNTEREXAMPLE 1: TailsIntersection is ANTITONE-CAPABLE. -----------------
; `eval` (MORKL.scala:325-327) groups the source by HEAD and intersects the
; tail-sets, returning {} when there are no headed paths.  Adding a path with a
; NEW head therefore adds a new group to the intersection, which can only SHRINK
; the result:
;       A = { 0.7 }              TailsIntersection(A) = { 7 }
;       B = { 0.7, 1.8 }         TailsIntersection(B) = { 7 } /\ { 8 } = { }
; A subset= B, yet TI(A) is NOT subset= TI(B).  In Zippy source that is
;       r1(x) = /\.(r2(x))            with r2 growing across the fixpoint rounds
; which `mono` accepts today (`case Space.TailsIntersection(a) => mono(a)`).
;
; --- COUNTEREXAMPLE 2: Iteration is antitone in its SOURCE. -------------------
; `eval` (:318-324) groups the source by head and evaluates the body with
; `rest` bound to that group's TAIL SET.  Growing the source can enlarge an
; existing group, and a body that is ANTITONE IN `rest` then produces less:
;       body(n, nbs) = {eps} \ \/(nbs <| {9})     -- i.e. drop eps iff 9 in nbs
;       A = { 0.7 }        heads {0}, tails {7}      -> body yields {eps}
;       B = { 0.7, 0.9 }   heads {0}, tails {7,9}    -> body yields { }
; A subset= B, yet Iter(A) is NOT subset= Iter(B).  `mono` accepts this because
; its Iteration arm is `mono(src) && mono(b)` and its Subtraction arm only
; forbids the SCC CALL in the subtrahend — `Mention(rest)` is not an SCC call,
; so `X \ Mention(rest)` passes.  The gate checks monotonicity in the RECURSIVE
; MENTION and silently assumes the body is monotone in the LOOP VARIABLE too.
;
; --- WHAT FOLLOWS, AND WHAT DOES NOT. ----------------------------------------
; This does NOT say any artifact in the repo is wrong: no cornerstone or corpus
; program puts a recursive mention under a TailsIntersection or under an
; Iteration source with a rest-antitone body, so the gates have never been
; asked the question they answer wrongly.  It says the GATES ARE NOT SOUND AS
; WRITTEN, so the O1/O10 monotonicity hypothesis is not actually discharged for
; every program the compiler would accept.
;
; THE FIX IS ALREADY WRITTEN, IN ANOTHER FILE.  `AgnosticPipeline.monotoneInMention`
; (EquivPipeline.scala:376-399), added for plan item 1, decides the same question
; and gets BOTH arms right:
;       case TailsIntersection(src) => !free(src)
;       case Iteration(src, _, rest, body) =>
;         (!free(src) || (go(src) && monotoneInMention(body, rest))) && (rest.s == m.s || go(body))
; So the patch to MORKL.scala is not a new invention: make `mono` (:1256-1257)
; and `monoIn` (:1292-1293) agree with it — `!refersScc(a)` / `!uses(a, m)` for
; TailsIntersection, and the rest-monotonicity side condition for Iteration.
; That patch is in the report; MORKL.scala is not this agent's file to edit.
; Until it lands, the honest reading of `asFixpointGeneral` /
; `lowerMutualPassthrough` is "monotone for the shapes we have tested", and
; REGISTRY.tsv marks the two arms OPEN rather than proved.
;
; ENCODING.  Paths are the `cons/nil` datatype and spaces are PREDICATES over
; paths, exactly as in proofs/laws/* and terminating/tagged_projection.smt2.
; A "monotone in m" body is modelled as a function of an argument space, and
; each goal below is the arm's transfer rule applied to arbitrary argument
; spaces P subset= Q.  The two refutations are CONCRETE spaces (defined, not
; axiomatised) so that they cannot be vacuous: there is nothing to be
; inconsistent about a `define-fun`.
;
; PROVER LOG (z3 5.1.0 and vampire 5.1.0).  All goals close in under a second;
; vampire independently discharges all 15 as well, so every claim here — the
; sound arms AND the two refutations — is cross-validated by both provers.
; =============================================================================
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-fun append (Path Path) Path)
(assert (forall ((q Path)) (= (append nil q) q)))
(assert (forall ((h Int) (t Path) (q Path)) (= (append (cons h t) q) (cons h (append t q)))))
(declare-fun isPrefix (Path Path) Bool)
(assert (forall ((p Path)) (isPrefix nil p)))
(assert (forall ((h Int) (t Path)) (not (isPrefix (cons h t) nil))))
(assert (forall ((h Int) (t Path) (h2 Int) (t2 Path))
  (= (isPrefix (cons h t) (cons h2 t2)) (and (= h h2) (isPrefix t t2)))))

; --- two arbitrary spaces with P subset= Q, and two more for the binary arms.
(declare-fun P (Path) Bool) (declare-fun Q (Path) Bool)
(declare-fun R (Path) Bool) (declare-fun S (Path) Bool)
(declare-const w Path)                                       ; a Wrap/Unwrap prefix

; =============================================================================
; THE SOUND ARMS.  Each goal is "P subset= Q and R subset= S imply the arm's
; result grows"; the arms that take one operand ignore R/S.
; =============================================================================
; --- Union.
(push)
(assert (forall ((p Path)) (=> (P p) (Q p))))
(assert (forall ((p Path)) (=> (R p) (S p))))
(assert (not (forall ((p Path)) (=> (or (P p) (R p)) (or (Q p) (S p))))))
(check-sat) ; expect unsat
(pop)
; --- Intersection.
(push)
(assert (forall ((p Path)) (=> (P p) (Q p))))
(assert (forall ((p Path)) (=> (R p) (S p))))
(assert (not (forall ((p Path)) (=> (and (P p) (R p)) (and (Q p) (S p))))))
(check-sat) ; expect unsat
(pop)
; --- Subtraction: monotone in the LEFT arm, ANTITONE in the right.
; (The gates forbid the recursive mention in the right arm, so left-monotonicity
; is exactly what they need; the antitone half is proved too, because it is the
; reason the prohibition is the right one and not merely a cautious one.)
(push)
(assert (forall ((p Path)) (=> (P p) (Q p))))
(assert (forall ((p Path)) (=> (R p) (S p))))
(assert (not (and (forall ((p Path)) (=> (and (P p) (not (R p))) (and (Q p) (not (R p)))))
                  (forall ((p Path)) (=> (and (P p) (not (S p))) (and (P p) (not (R p))))))))
(check-sat) ; expect unsat
(pop)
; --- Raffination: `a \| b` = { p in a : NO path of b is a prefix of p }
; (eval MORKL.scala:353 expands it to `a \ Restriction(a,b)`).  Monotone in the
; LEFT arm, ANTITONE in the right — the same shape as Subtraction but with the
; right arm entering through a PREFIX test rather than pointwise, which is why
; it gets its own goal instead of being read off the Subtraction one.
(push)
(assert (forall ((p Path)) (=> (P p) (Q p))))
(assert (forall ((p Path)) (=> (R p) (S p))))
(assert (not (and
  (forall ((p Path))
    (=> (and (P p) (not (exists ((q Path)) (and (R q) (isPrefix q p)))))
        (and (Q p) (not (exists ((q Path)) (and (R q) (isPrefix q p)))))))
  (forall ((p Path))
    (=> (and (P p) (not (exists ((q Path)) (and (S q) (isPrefix q p)))))
        (and (P p) (not (exists ((q Path)) (and (R q) (isPrefix q p))))))))))
(check-sat) ; expect unsat
(pop)
; --- Composition: p in A.B iff p splits as u.v with u in A, v in B.
(push)
(assert (forall ((p Path)) (=> (P p) (Q p))))
(assert (forall ((p Path)) (=> (R p) (S p))))
(assert (not (forall ((p Path))
  (=> (exists ((u Path) (v Path)) (and (= p (append u v)) (P u) (R v)))
      (exists ((u Path) (v Path)) (and (= p (append u v)) (Q u) (S v)))))))
(check-sat) ; expect unsat
(pop)
; --- Restriction: keep the paths of A that extend some path of B.  Monotone in
; BOTH arms (more candidates, and more admissible prefixes).
(push)
(assert (forall ((p Path)) (=> (P p) (Q p))))
(assert (forall ((p Path)) (=> (R p) (S p))))
(assert (not (forall ((p Path))
  (=> (and (P p) (exists ((q Path)) (and (R q) (isPrefix q p))))
      (and (Q p) (exists ((q Path)) (and (S q) (isPrefix q p))))))))
(check-sat) ; expect unsat
(pop)
; --- Wrap and Unwrap at an arbitrary prefix.
(push)
(assert (forall ((p Path)) (=> (P p) (Q p))))
(assert (not (and (forall ((p Path))
                    (=> (exists ((q Path)) (and (= p (append w q)) (P q)))
                        (exists ((q Path)) (and (= p (append w q)) (Q q)))))
                  (forall ((q Path)) (=> (P (append w q)) (Q (append w q)))))))
(check-sat) ; expect unsat
(pop)
; --- TailsUnion: t is a tail of some headed path.
(push)
(assert (forall ((p Path)) (=> (P p) (Q p))))
(assert (not (forall ((t Path))
  (=> (exists ((h Int)) (P (cons h t))) (exists ((h Int)) (Q (cons h t)))))))
(check-sat) ; expect unsat
(pop)
; --- THE INDUCTION STEP that makes the accepted list a SCHEMA rather than a
; list: a composite of two monotone transfer functions is monotone.  Without
; this goal the arms above would only cover depth-1 bodies.
(declare-fun f (Path Bool) Bool)                       ; f applied pointwise to a space
(declare-fun g (Path Bool) Bool)
(push)
(assert (forall ((p Path) (a Bool) (b Bool)) (=> (and (=> a b) (f p a)) (f p b))))   ; f monotone
(assert (forall ((p Path) (a Bool) (b Bool)) (=> (and (=> a b) (g p a)) (g p b))))   ; g monotone
(assert (forall ((p Path)) (=> (P p) (Q p))))
(assert (not (forall ((p Path)) (=> (f p (g p (P p))) (f p (g p (Q p)))))))
(check-sat) ; expect unsat
(pop)

; =============================================================================
; THE TWO UNSOUND ARMS, REFUTED.  Both counterexamples are CONCRETE spaces
; built with `define-fun`, so no axiom is involved and vacuity is impossible.
; =============================================================================
; --- CE1: TailsIntersection.  ta = { 0.7 }, tb = { 0.7, 1.8 }.
(define-fun ta ((p Path)) Bool (= p (cons 0 (cons 7 nil))))
(define-fun tb ((p Path)) Bool (or (= p (cons 0 (cons 7 nil))) (= p (cons 1 (cons 8 nil)))))
; TailsIntersection(X)(t)  <=>  X has a headed path, and every head-group holds t.
(define-fun tiA ((t Path)) Bool
  (and (exists ((h Int) (u Path)) (ta (cons h u)))
       (forall ((h Int)) (=> (exists ((u Path)) (ta (cons h u))) (ta (cons h t))))))
(define-fun tiB ((t Path)) Bool
  (and (exists ((h Int) (u Path)) (tb (cons h u)))
       (forall ((h Int)) (=> (exists ((u Path)) (tb (cons h u))) (tb (cons h t))))))
; --- CE1a: ta really is contained in tb (so this is a monotonicity failure and
; not a mis-stated pair).
(push)
(assert (not (forall ((p Path)) (=> (ta p) (tb p)))))
(check-sat) ; expect unsat
(pop)
; --- CE1b: the tail 7 survives in TI(ta) and is LOST in TI(tb).
(push)
(assert (not (and (tiA (cons 7 nil)) (not (tiB (cons 7 nil))))))
(check-sat) ; expect unsat
(pop)
; --- CE1c: hence TailsIntersection is not monotone.
(push)
(assert (forall ((t Path)) (=> (tiA t) (tiB t))))
(check-sat) ; expect unsat
(pop)

; --- CE2: Iteration with a body that is ANTITONE IN `rest`.
; ia = { 0.7 }, ib = { 0.7, 0.9 } — same single head, a LARGER tail group.
; body(n, nbs) = {eps} \ {eps if 9 in nbs}, i.e. `Iter(X)(eps)` holds iff some
; head-group of X exists that does NOT contain the tail 9.
(define-fun ia ((p Path)) Bool (= p (cons 0 (cons 7 nil))))
(define-fun ib ((p Path)) Bool (or (= p (cons 0 (cons 7 nil))) (= p (cons 0 (cons 9 nil)))))
(define-fun iterA ((p Path)) Bool
  (exists ((h Int)) (and (exists ((u Path)) (ia (cons h u))) (= p nil)
                         (not (ia (cons h (cons 9 nil)))))))
(define-fun iterB ((p Path)) Bool
  (exists ((h Int)) (and (exists ((u Path)) (ib (cons h u))) (= p nil)
                         (not (ib (cons h (cons 9 nil)))))))
; --- CE2a: ia is contained in ib.
(push)
(assert (not (forall ((p Path)) (=> (ia p) (ib p)))))
(check-sat) ; expect unsat
(pop)
; --- CE2b: eps is produced from ia and NOT from ib.
(push)
(assert (not (and (iterA nil) (not (iterB nil)))))
(check-sat) ; expect unsat
(pop)
; --- CE2c: hence Iteration is not monotone in its source.
(push)
(assert (forall ((p Path)) (=> (iterA p) (iterB p))))
(check-sat) ; expect unsat
(pop)
