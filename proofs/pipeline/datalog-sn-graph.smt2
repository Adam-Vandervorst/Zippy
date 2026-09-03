; PROVER LOG (both provers are run on every obligation; verdicts also in STATUS.tsv)
; ∀-path goal            z3 unsat           9 ms   vampire refutation      6 ms (budget 60s each)
; AUTO-GENERATED — pipeline stage 3 (datalog-sn): graph vs space (∀ paths)
; INSTANCE leg: the inputs are this instance's literals, but the CONTROL FLOW IS NOT EXECUTED —
; `Iteration` stays a binder (its group predicate inlined) and `Fixpoint` stays the least
; post-fixpoint predicate with the two axioms plus Park induction, so the two sides are
; independently rendered PROGRAMS rather than the same precomputed literal.
; The goal (negated): the programs produce the SAME OUTPUT — equal membership at EVERY path.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))


(define-fun s_2 ((p Path)) Bool (or (or (= p (cons 12302 (cons 12303 nil))) (= p (cons 12302 (cons 12305 nil))) (= p (cons 12303 (cons 12304 nil))) (= p (cons 12305 (cons 12303 nil))) (= p (cons 12305 (cons 12304 nil)))) (or (= p (cons 12302 (cons 12303 nil))) (= p (cons 12302 (cons 12304 nil))) (= p (cons 12302 (cons 12305 nil))) (= p (cons 12303 (cons 12304 nil))) (= p (cons 12305 (cons 12303 nil))) (= p (cons 12305 (cons 12304 nil))))))
(define-fun s_1 ((p Path)) Bool (or (or (= p (cons 12302 (cons 12305 nil))) (= p (cons 12303 (cons 12304 nil))) (= p (cons 12305 (cons 12303 nil)))) (s_2 p)))
(define-fun s_5 ((p Path)) Bool (or (or (= p (cons 12302 (cons 12303 nil))) (= p (cons 12302 (cons 12304 nil))) (= p (cons 12302 (cons 12305 nil))) (= p (cons 12303 (cons 12304 nil))) (= p (cons 12305 (cons 12303 nil))) (= p (cons 12305 (cons 12304 nil)))) (or (= p (cons 12302 (cons 12303 nil))) (= p (cons 12302 (cons 12304 nil))) (= p (cons 12302 (cons 12305 nil))) (= p (cons 12303 (cons 12304 nil))) (= p (cons 12305 (cons 12303 nil))) (= p (cons 12305 (cons 12304 nil))))))
(define-fun s_4 ((p Path)) Bool (or (or (= p (cons 12302 (cons 12303 nil))) (= p (cons 12302 (cons 12305 nil))) (= p (cons 12303 (cons 12304 nil))) (= p (cons 12305 (cons 12303 nil))) (= p (cons 12305 (cons 12304 nil)))) (s_5 p)))
(define-fun s_3 ((p Path)) Bool (or (or (= p (cons 12302 (cons 12305 nil))) (= p (cons 12303 (cons 12304 nil))) (= p (cons 12305 (cons 12303 nil)))) (s_4 p)))
(define-fun sideA ((p Path)) Bool (s_1 p))
(define-fun sideB ((p Path)) Bool (s_3 p))
(assert (not (forall ((p Path)) (= (sideA p) (sideB p)))))
(check-sat)
