; AUTO-GENERATED — pipeline stage 2 (aunt): zipper vs space (instance observations, folded)
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

(define-fun m_1 ((p Path)) Bool (or (= p (cons 227 (cons 216 (cons 223 nil)))) (= p (cons 227 (cons 217 (cons 226 nil)))) (= p (cons 227 (cons 226 (cons 223 nil))))))
(define-fun m_2 ((p Path)) Bool (or (= p (cons 227 (cons 216 (cons 223 nil)))) (= p (cons 227 (cons 217 (cons 226 nil)))) (= p (cons 227 (cons 226 (cons 223 nil))))))

(assert (not (and (= (m_1 (cons 227 (cons 216 (cons 223 nil)))) (m_2 (cons 227 (cons 216 (cons 223 nil))))) (= (m_1 (cons 227 (cons 217 (cons 226 nil)))) (m_2 (cons 227 (cons 217 (cons 226 nil))))) (= (m_1 (cons 227 (cons 226 (cons 223 nil)))) (m_2 (cons 227 (cons 226 (cons 223 nil))))) (= (m_1 (cons 215 nil)) (m_2 (cons 215 nil))) (= (m_1 (cons 216 nil)) (m_2 (cons 216 nil))) (= (m_1 (cons 217 nil)) (m_2 (cons 217 nil))) (= (m_1 (cons 218 nil)) (m_2 (cons 218 nil))) (= (m_1 (cons 219 nil)) (m_2 (cons 219 nil))) (= (m_1 (cons 220 nil)) (m_2 (cons 220 nil))) (= (m_1 (cons 221 nil)) (m_2 (cons 221 nil))) (= (m_1 (cons 222 nil)) (m_2 (cons 222 nil))) (= (m_1 (cons 223 nil)) (m_2 (cons 223 nil))) (= (m_1 (cons 224 nil)) (m_2 (cons 224 nil))) (= (m_1 (cons 225 nil)) (m_2 (cons 225 nil))) (= (m_1 (cons 226 nil)) (m_2 (cons 226 nil))) (= (m_1 (cons 227 (cons 215 nil))) (m_2 (cons 227 (cons 215 nil)))) (= (m_1 (cons 227 (cons 218 nil))) (m_2 (cons 227 (cons 218 nil)))) (= (m_1 (cons 227 (cons 219 nil))) (m_2 (cons 227 (cons 219 nil)))) (= (m_1 (cons 227 (cons 220 nil))) (m_2 (cons 227 (cons 220 nil)))) (= (m_1 (cons 227 (cons 221 nil))) (m_2 (cons 227 (cons 221 nil)))) (= (m_1 (cons 227 (cons 222 nil))) (m_2 (cons 227 (cons 222 nil)))) (= (m_1 (cons 227 (cons 223 nil))) (m_2 (cons 227 (cons 223 nil)))) (= (m_1 (cons 227 (cons 224 nil))) (m_2 (cons 227 (cons 224 nil)))) (= (m_1 (cons 227 (cons 225 nil))) (m_2 (cons 227 (cons 225 nil)))) (= (m_1 (cons 227 (cons 227 nil))) (m_2 (cons 227 (cons 227 nil)))) (= (m_1 (cons 227 (cons 216 (cons 215 nil)))) (m_2 (cons 227 (cons 216 (cons 215 nil))))) (= (m_1 (cons 227 (cons 216 (cons 216 nil)))) (m_2 (cons 227 (cons 216 (cons 216 nil))))) (= (m_1 (cons 227 (cons 216 (cons 217 nil)))) (m_2 (cons 227 (cons 216 (cons 217 nil))))))))
(check-sat)
