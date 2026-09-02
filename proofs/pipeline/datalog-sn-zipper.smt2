; PROVER LOG (both provers are run on every obligation; verdicts also in STATUS.tsv)
; ∀-path goal            z3 unsat           9 ms   vampire refutation      6 ms (budget 60s each)
; AUTO-GENERATED — pipeline stage 2 (datalog-sn): zipper vs space (∀ paths)
; Both sides compiled to their denotational membership formulas over the same inputs;
; the goal (negated): the programs produce the SAME OUTPUT — equal membership at EVERY path.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))

(define-fun m_1 ((p Path)) Bool (or (= p (cons 31 (cons 37 nil))) (= p (cons 32 (cons 31 nil))) (= p (cons 32 (cons 33 nil))) (= p (cons 32 (cons 37 nil))) (= p (cons 33 (cons 31 nil))) (= p (cons 33 (cons 37 nil)))))
(define-fun m_3 ((p Path)) Bool (or (= p (cons 31 (cons 37 nil))) (= p (cons 32 (cons 33 nil))) (= p (cons 33 (cons 31 nil)))))
(define-fun m_5 ((p Path)) Bool (or (= p (cons 31 (cons 37 nil))) (= p (cons 32 (cons 31 nil))) (= p (cons 32 (cons 33 nil))) (= p (cons 33 (cons 31 nil))) (= p (cons 33 (cons 37 nil)))))
(define-fun m_6 ((p Path)) Bool (or (m_1 p) (m_1 p)))
(define-fun m_4 ((p Path)) Bool (or (m_5 p) (m_6 p)))
(define-fun m_2 ((p Path)) Bool (or (m_3 p) (m_4 p)))

(assert (not (forall ((p Path)) (= (m_1 p) (m_2 p)))))
(check-sat)
