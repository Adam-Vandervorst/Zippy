; THE POSITIVE SIDE of the fixpoint_is_lfp.smt2:47-50 differential.  The FIRST-CLASS
; `Fixpoint` denotation (post-fixpoint axioms + Park induction, EquivPipeline.AgSmt.fixSym)
; is asked to equal {a,b,c} — the brute-forced least post-fixpoint above init, which is
; ALSO what every executor now returns.  Expected: unsat / Refutation found.
; AUTO-GENERATED — fixpoint_is_lfp counterexample — lfp_agrees.smt2
; DATA-AGNOSTIC: inputs are uninterpreted path-set predicates; the goal (negated) states the two
; programs produce the same output at EVERY path for ALL inputs.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-fun append (Path Path) Path)
(assert (forall ((q Path)) (= (append nil q) q)))
(assert (forall ((h Int) (t Path) (q Path)) (= (append (cons h t) q) (cons h (append t q)))))
; certified lemmas (proofs/lemma_append_cons.smt2, proofs/lemma_append_nil.smt2 — both PROVED)
(assert (forall ((k2 Int) (p Path) (q Path) (r Path))
  (= (= (cons k2 p) (append q r))
     (or (and (= q nil) (= r (cons k2 p)))
         (exists ((q2 Path)) (and (= q (cons k2 q2)) (= p (append q2 r))))))))
(assert (forall ((q Path)) (= (append q nil) q)))
(declare-fun isPrefix (Path Path) Bool)
(assert (forall ((p Path)) (isPrefix nil p)))
(assert (forall ((h Int) (t Path)) (not (isPrefix (cons h t) nil))))
(assert (forall ((h Int) (t Path) (h2 Int) (t2 Path))
  (= (isPrefix (cons h t) (cons h2 t2)) (and (= h h2) (isPrefix t t2)))))

(declare-fun fix_2 (Path) Bool)
; FIXPOINT fix_2 — first-class: the LEAST post-fixpoint above init (never unrolled)
(assert (forall ((zq Path)) (=> (or (= zq (cons 0 nil))) (fix_2 zq))))
(assert (forall ((zq Path)) (=> (or (exists ((q_3 Path)) (and (= zq (cons 1 q_3)) (and (fix_2 (cons 0 q_3)) (or (= (cons 0 q_3) (cons 0 nil)))))) (exists ((q_4 Path)) (and (= zq (cons 2 q_4)) (and (and (fix_2 (cons 0 q_4)) (or (= (cons 0 q_4) (cons 0 nil)))) (and (fix_2 (cons 1 q_4)) (or (= (cons 1 q_4) (cons 1 nil)))))))) (fix_2 zq))))
(define-fun s_1 ((p Path)) Bool (fix_2 p))
(define-fun sideA ((p Path)) Bool (s_1 p))
(define-fun sideB ((p Path)) Bool (or (= p (cons 0 nil)) (= p (cons 1 nil)) (= p (cons 2 nil))))
; PARK INDUCTION fix_2 ⊑ sideA — leastness of fix_2; BOTH premises are obligations
(assert (=> (and (forall ((zr Path)) (=> (or (= zr (cons 0 nil))) (sideA zr))) (forall ((zr Path)) (=> (or (exists ((q_5 Path)) (and (= zr (cons 1 q_5)) (and (sideA (cons 0 q_5)) (or (= (cons 0 q_5) (cons 0 nil)))))) (exists ((q_6 Path)) (and (= zr (cons 2 q_6)) (and (and (sideA (cons 0 q_6)) (or (= (cons 0 q_6) (cons 0 nil)))) (and (sideA (cons 1 q_6)) (or (= (cons 1 q_6) (cons 1 nil)))))))) (sideA zr)))) (forall ((zq Path)) (=> (fix_2 zq) (sideA zq)))))
; PARK INDUCTION fix_2 ⊑ sideB — leastness of fix_2; BOTH premises are obligations
(assert (=> (and (forall ((zr Path)) (=> (or (= zr (cons 0 nil))) (sideB zr))) (forall ((zr Path)) (=> (or (exists ((q_7 Path)) (and (= zr (cons 1 q_7)) (and (sideB (cons 0 q_7)) (or (= (cons 0 q_7) (cons 0 nil)))))) (exists ((q_8 Path)) (and (= zr (cons 2 q_8)) (and (and (sideB (cons 0 q_8)) (or (= (cons 0 q_8) (cons 0 nil)))) (and (sideB (cons 1 q_8)) (or (= (cons 1 q_8) (cons 1 nil)))))))) (sideB zr)))) (forall ((zq Path)) (=> (fix_2 zq) (sideB zq)))))
(assert (not (forall ((p Path)) (= (sideA p) (sideB p)))))
(check-sat)
