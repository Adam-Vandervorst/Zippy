; AUTO-GENERATED — pipeline stage 2 (puzzle15): zipper vs space (instance observations, folded)
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

(define-fun m_1 ((p Path)) Bool (or (= p (cons 263 (cons 166 (cons 167 (cons 169 (cons 168 (cons 163 (cons 164 (cons 170 (cons 178 (cons 173 (cons 174 (cons 171 (cons 172 (cons 175 (cons 176 (cons 177 nil))))))))))))))))) (= p (cons 266 (cons 168 (cons 166 (cons 167 (cons 169 (cons 163 (cons 164 (cons 170 (cons 178 (cons 173 (cons 174 (cons 171 (cons 172 (cons 175 (cons 176 (cons 177 nil)))))))))))))))))))
(define-fun m_2 ((p Path)) Bool (or (= p (cons 263 (cons 166 (cons 167 (cons 169 (cons 168 (cons 163 (cons 164 (cons 170 (cons 178 (cons 173 (cons 174 (cons 171 (cons 172 (cons 175 (cons 176 (cons 177 nil))))))))))))))))) (= p (cons 266 (cons 168 (cons 166 (cons 167 (cons 169 (cons 163 (cons 164 (cons 170 (cons 178 (cons 173 (cons 174 (cons 171 (cons 172 (cons 175 (cons 176 (cons 177 nil)))))))))))))))))))

(assert (not (and (= (m_1 (cons 263 (cons 166 (cons 167 (cons 169 (cons 168 (cons 163 (cons 164 (cons 170 (cons 178 (cons 173 (cons 174 (cons 171 (cons 172 (cons 175 (cons 176 (cons 177 nil))))))))))))))))) (m_2 (cons 263 (cons 166 (cons 167 (cons 169 (cons 168 (cons 163 (cons 164 (cons 170 (cons 178 (cons 173 (cons 174 (cons 171 (cons 172 (cons 175 (cons 176 (cons 177 nil)))))))))))))))))) (= (m_1 (cons 266 (cons 168 (cons 166 (cons 167 (cons 169 (cons 163 (cons 164 (cons 170 (cons 178 (cons 173 (cons 174 (cons 171 (cons 172 (cons 175 (cons 176 (cons 177 nil))))))))))))))))) (m_2 (cons 266 (cons 168 (cons 166 (cons 167 (cons 169 (cons 163 (cons 164 (cons 170 (cons 178 (cons 173 (cons 174 (cons 171 (cons 172 (cons 175 (cons 176 (cons 177 nil)))))))))))))))))) (= (m_1 (cons 163 nil)) (m_2 (cons 163 nil))) (= (m_1 (cons 164 nil)) (m_2 (cons 164 nil))) (= (m_1 (cons 166 nil)) (m_2 (cons 166 nil))) (= (m_1 (cons 167 nil)) (m_2 (cons 167 nil))) (= (m_1 (cons 168 nil)) (m_2 (cons 168 nil))) (= (m_1 (cons 169 nil)) (m_2 (cons 169 nil))) (= (m_1 (cons 170 nil)) (m_2 (cons 170 nil))) (= (m_1 (cons 171 nil)) (m_2 (cons 171 nil))) (= (m_1 (cons 172 nil)) (m_2 (cons 172 nil))) (= (m_1 (cons 173 nil)) (m_2 (cons 173 nil))) (= (m_1 (cons 174 nil)) (m_2 (cons 174 nil))) (= (m_1 (cons 175 nil)) (m_2 (cons 175 nil))) (= (m_1 (cons 176 nil)) (m_2 (cons 176 nil))) (= (m_1 (cons 177 nil)) (m_2 (cons 177 nil))) (= (m_1 (cons 178 nil)) (m_2 (cons 178 nil))) (= (m_1 (cons 261 nil)) (m_2 (cons 261 nil))) (= (m_1 (cons 262 nil)) (m_2 (cons 262 nil))) (= (m_1 (cons 264 nil)) (m_2 (cons 264 nil))) (= (m_1 (cons 265 nil)) (m_2 (cons 265 nil))) (= (m_1 (cons 267 nil)) (m_2 (cons 267 nil))) (= (m_1 (cons 268 nil)) (m_2 (cons 268 nil))) (= (m_1 (cons 269 nil)) (m_2 (cons 269 nil))) (= (m_1 (cons 270 nil)) (m_2 (cons 270 nil))) (= (m_1 (cons 5454 nil)) (m_2 (cons 5454 nil))) (= (m_1 (cons 5455 nil)) (m_2 (cons 5455 nil))))))
(check-sat)
