; PROVER LOG (both provers are run on every obligation; verdicts also in STATUS.tsv)
; ∀-path goal            z3 unsat      vampire refutation (budget 60s each; timings are in the run log, not here — a wall clock in a committed artifact makes it differ from itself on every run)
; AUTO-GENERATED — pipeline stage 3 (datalog-sn): graph vs space (∀ paths)
; INSTANCE leg: the inputs are this instance's literals, but the CONTROL FLOW IS NOT EXECUTED —
; `Iteration` stays a binder (its group predicate inlined) and `Fixpoint` stays the least
; post-fixpoint predicate with the two axioms plus Park induction, so the two sides are
; independently rendered PROGRAMS rather than the same precomputed literal.
; The goal (negated): the programs produce the SAME OUTPUT — equal membership at EVERY path.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))


(define-fun s_2 ((p Path)) Bool (or (or (= p (cons 15 (cons 16 nil))) (= p (cons 17 (cons 15 nil))) (= p (cons 17 (cons 16 nil))) (= p (cons 18 (cons 15 nil))) (= p (cons 18 (cons 17 nil)))) (or (= p (cons 15 (cons 16 nil))) (= p (cons 17 (cons 15 nil))) (= p (cons 17 (cons 16 nil))) (= p (cons 18 (cons 15 nil))) (= p (cons 18 (cons 16 nil))) (= p (cons 18 (cons 17 nil))))))
(define-fun s_1 ((p Path)) Bool (or (or (= p (cons 15 (cons 16 nil))) (= p (cons 17 (cons 15 nil))) (= p (cons 18 (cons 17 nil)))) (s_2 p)))
(define-fun s_5 ((p Path)) Bool (or (or (= p (cons 15 (cons 16 nil))) (= p (cons 17 (cons 15 nil))) (= p (cons 17 (cons 16 nil))) (= p (cons 18 (cons 15 nil))) (= p (cons 18 (cons 16 nil))) (= p (cons 18 (cons 17 nil)))) (or (= p (cons 15 (cons 16 nil))) (= p (cons 17 (cons 15 nil))) (= p (cons 17 (cons 16 nil))) (= p (cons 18 (cons 15 nil))) (= p (cons 18 (cons 16 nil))) (= p (cons 18 (cons 17 nil))))))
(define-fun s_4 ((p Path)) Bool (or (or (= p (cons 15 (cons 16 nil))) (= p (cons 17 (cons 15 nil))) (= p (cons 17 (cons 16 nil))) (= p (cons 18 (cons 15 nil))) (= p (cons 18 (cons 17 nil)))) (s_5 p)))
(define-fun s_3 ((p Path)) Bool (or (or (= p (cons 15 (cons 16 nil))) (= p (cons 17 (cons 15 nil))) (= p (cons 18 (cons 17 nil)))) (s_4 p)))
(define-fun sideA ((p Path)) Bool (s_1 p))
(define-fun sideB ((p Path)) Bool (s_3 p))
(assert (not (forall ((p Path)) (= (sideA p) (sideB p)))))
(check-sat)
