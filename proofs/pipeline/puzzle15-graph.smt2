; AUTO-GENERATED — pipeline stage 3 (puzzle15): graph vs space (instance observations, folded)
; Both sides compiled to their denotational membership formulas over the same inputs;
; the goal (negated): the programs produce the SAME OUTPUT — equal membership at every path.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-fun append (Path Path) Path)
(assert (forall ((q Path)) (= (append nil q) q)))
(assert (forall ((h Int) (t Path) (q Path)) (= (append (cons h t) q) (cons h (append t q)))))
(declare-fun isPrefix (Path Path) Bool)
(assert (forall ((p Path)) (isPrefix nil p)))
(assert (forall ((h Int) (t Path)) (not (isPrefix (cons h t) nil))))
(assert (forall ((h Int) (t Path) (h2 Int) (t2 Path))
  (= (isPrefix (cons h t) (cons h2 t2)) (and (= h h2) (isPrefix t t2)))))
; certified lemmas (proofs/lemma_append_cons.smt2, proofs/lemma_append_nil.smt2 — both PROVED)
(assert (forall ((k2 Int) (p Path) (q Path) (r Path))
  (= (= (cons k2 p) (append q r))
     (or (and (= q nil) (= r (cons k2 p)))
         (exists ((q2 Path)) (and (= q (cons k2 q2)) (= p (append q2 r))))))))
(assert (forall ((q Path)) (= (append q nil) q)))

(define-fun m_1 ((p Path)) Bool (or (= p (cons 43 (cons 17 (cons 15 (cons 16 (cons 20 (cons 60 (cons 61 (cons 62 (cons 63 (cons 64 (cons 65 (cons 66 (cons 67 (cons 68 (cons 69 (cons 70 nil))))))))))))))))) (= p (cons 56 (cons 20 (cons 17 (cons 15 (cons 16 (cons 60 (cons 61 (cons 62 (cons 63 (cons 64 (cons 65 (cons 66 (cons 67 (cons 68 (cons 69 (cons 70 nil)))))))))))))))))))
(define-fun m_2 ((p Path)) Bool (or (= p (cons 43 (cons 17 (cons 15 (cons 16 (cons 20 (cons 60 (cons 61 (cons 62 (cons 63 (cons 64 (cons 65 (cons 66 (cons 67 (cons 68 (cons 69 (cons 70 nil))))))))))))))))) (= p (cons 56 (cons 20 (cons 17 (cons 15 (cons 16 (cons 60 (cons 61 (cons 62 (cons 63 (cons 64 (cons 65 (cons 66 (cons 67 (cons 68 (cons 69 (cons 70 nil)))))))))))))))))))

(assert (not (and (= (m_1 (cons 43 (cons 17 (cons 15 (cons 16 (cons 20 (cons 60 (cons 61 (cons 62 (cons 63 (cons 64 (cons 65 (cons 66 (cons 67 (cons 68 (cons 69 (cons 70 nil))))))))))))))))) (m_2 (cons 43 (cons 17 (cons 15 (cons 16 (cons 20 (cons 60 (cons 61 (cons 62 (cons 63 (cons 64 (cons 65 (cons 66 (cons 67 (cons 68 (cons 69 (cons 70 nil)))))))))))))))))) (= (m_1 (cons 56 (cons 20 (cons 17 (cons 15 (cons 16 (cons 60 (cons 61 (cons 62 (cons 63 (cons 64 (cons 65 (cons 66 (cons 67 (cons 68 (cons 69 (cons 70 nil))))))))))))))))) (m_2 (cons 56 (cons 20 (cons 17 (cons 15 (cons 16 (cons 60 (cons 61 (cons 62 (cons 63 (cons 64 (cons 65 (cons 66 (cons 67 (cons 68 (cons 69 (cons 70 nil)))))))))))))))))) (= (m_1 (cons 15 nil)) (m_2 (cons 15 nil))) (= (m_1 (cons 16 nil)) (m_2 (cons 16 nil))) (= (m_1 (cons 17 nil)) (m_2 (cons 17 nil))) (= (m_1 (cons 20 nil)) (m_2 (cons 20 nil))) (= (m_1 (cons 42 nil)) (m_2 (cons 42 nil))) (= (m_1 (cons 44 nil)) (m_2 (cons 44 nil))) (= (m_1 (cons 45 nil)) (m_2 (cons 45 nil))) (= (m_1 (cons 46 nil)) (m_2 (cons 46 nil))) (= (m_1 (cons 47 nil)) (m_2 (cons 47 nil))) (= (m_1 (cons 48 nil)) (m_2 (cons 48 nil))) (= (m_1 (cons 49 nil)) (m_2 (cons 49 nil))) (= (m_1 (cons 50 nil)) (m_2 (cons 50 nil))) (= (m_1 (cons 51 nil)) (m_2 (cons 51 nil))) (= (m_1 (cons 52 nil)) (m_2 (cons 52 nil))) (= (m_1 (cons 53 nil)) (m_2 (cons 53 nil))) (= (m_1 (cons 54 nil)) (m_2 (cons 54 nil))) (= (m_1 (cons 55 nil)) (m_2 (cons 55 nil))) (= (m_1 (cons 57 nil)) (m_2 (cons 57 nil))) (= (m_1 (cons 59 nil)) (m_2 (cons 59 nil))) (= (m_1 (cons 60 nil)) (m_2 (cons 60 nil))) (= (m_1 (cons 61 nil)) (m_2 (cons 61 nil))) (= (m_1 (cons 62 nil)) (m_2 (cons 62 nil))) (= (m_1 (cons 63 nil)) (m_2 (cons 63 nil))) (= (m_1 (cons 64 nil)) (m_2 (cons 64 nil))) (= (m_1 (cons 65 nil)) (m_2 (cons 65 nil))))))
(check-sat)
