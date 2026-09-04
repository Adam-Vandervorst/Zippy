; LEMMA: append q nil = q  (explicit structural-induction schema instance)
; paths are finite key sequences
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(define-fun-rec append ((p Path) (q Path)) Path
  (match p ((nil q) ((cons h t) (cons h (append t q))))))
; prefix r of p
(define-fun-rec isPrefix ((r Path) (p Path)) Bool
  (match r ((nil true)
            ((cons h t) (match p ((nil false)
                                  ((cons h2 t2) (and (= h h2) (isPrefix t t2)))))))))
(define-fun PN ((q Path)) Bool (= (append q nil) q))
; ASSUMED: T1
(assert (=> (and (PN nil) (forall ((k Int) (t Path)) (=> (PN t) (PN (cons k t))))) (forall ((q Path)) (PN q))))
(assert (not (forall ((q Path)) (PN q))))
(check-sat)
