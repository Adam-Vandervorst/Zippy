; PROVER LOG (both provers are run on every obligation; verdicts also in STATUS.tsv)
; ∀-path goal            z3 unsat          10 ms   vampire refutation     12 ms (budget 60s each)
; AUTO-GENERATED — pipeline stage 2 (gol): zipper vs space (∀ paths)
; INSTANCE leg: the inputs are this instance's literals, but the CONTROL FLOW IS NOT EXECUTED —
; `Iteration` stays a binder (its group predicate inlined) and `Fixpoint` stays the least
; post-fixpoint predicate with the two axioms plus Park induction, so the two sides are
; independently rendered PROGRAMS rather than the same precomputed literal.
; The goal (negated): the programs produce the SAME OUTPUT — equal membership at EVERY path.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))


(define-fun s_7 ((p Path)) Bool false)
(define-fun s_6 ((p Path)) Bool (and (s_7 p) (not (s_7 p))))
(define-fun s_9 ((p Path)) Bool (= p (cons 17 (cons 17 nil))))
(define-fun s_8 ((p Path)) Bool (and (s_9 p) (not (s_7 p))))
(define-fun s_5 ((p Path)) Bool (or (s_6 p) (s_8 p)))
(define-fun s_4 ((p Path)) Bool (or (s_5 p) (s_6 p)))
(define-fun s_15 ((p Path)) Bool (or (s_6 p) (s_6 p)))
(define-fun s_17 ((p Path)) Bool (= p (cons 18 (cons 17 nil))))
(define-fun s_16 ((p Path)) Bool (and (s_17 p) (not (s_7 p))))
(define-fun s_14 ((p Path)) Bool (or (s_15 p) (s_16 p)))
(define-fun s_13 ((p Path)) Bool (or (s_14 p) (s_6 p)))
(define-fun s_12 ((p Path)) Bool (or (s_13 p) (s_6 p)))
(define-fun s_20 ((p Path)) Bool (or (s_15 p) (s_6 p)))
(define-fun s_19 ((p Path)) Bool (or (s_20 p) (s_6 p)))
(define-fun s_18 ((p Path)) Bool (or (s_19 p) (s_6 p)))
(define-fun s_11 ((p Path)) Bool (or (s_12 p) (s_18 p)))
(define-fun s_25 ((p Path)) Bool (= p (cons 15 (cons 17 nil))))
(define-fun s_24 ((p Path)) Bool (and (s_25 p) (not (s_7 p))))
(define-fun s_23 ((p Path)) Bool (or (s_15 p) (s_24 p)))
(define-fun s_22 ((p Path)) Bool (or (s_23 p) (s_6 p)))
(define-fun s_21 ((p Path)) Bool (or (s_22 p) (s_6 p)))
(define-fun s_10 ((p Path)) Bool (or (s_11 p) (s_21 p)))
(define-fun s_3 ((p Path)) Bool (or (s_4 p) (s_10 p)))
(define-fun s_1 ((p Path)) Bool (exists ((q_2 Path)) (and (= p (cons 22 q_2)) (s_3 q_2))))
(define-fun sideA ((p Path)) Bool (or (= p (cons 22 (cons 15 (cons 17 nil)))) (= p (cons 22 (cons 17 (cons 17 nil)))) (= p (cons 22 (cons 18 (cons 17 nil))))))
(define-fun sideB ((p Path)) Bool (s_1 p))
(assert (not (forall ((p Path)) (= (sideA p) (sideB p)))))
(check-sat)
