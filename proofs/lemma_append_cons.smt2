; LEMMA (used by composition.smt2): cons k p = append q r  ⟺  q = nil ∧ r = cons k p
;                                                            ∨ ∃q2. q = cons k q2 ∧ p = append q2 r
; paths are finite key sequences
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(define-fun-rec append ((p Path) (q Path)) Path
  (match p ((nil q) ((cons h t) (cons h (append t q))))))
; prefix r of p
(define-fun-rec isPrefix ((r Path) (p Path)) Bool
  (match r ((nil true)
            ((cons h t) (match p ((nil false)
                                  ((cons h2 t2) (and (= h h2) (isPrefix t t2)))))))))
(declare-const k Int)
(assert (not (forall ((p Path) (q Path) (r Path))
  (= (= (cons k p) (append q r))
     (or (and (= q nil) (= r (cons k p)))
         (exists ((q2 Path)) (and (= q (cons k q2)) (= p (append q2 r)))))))))
(check-sat)
