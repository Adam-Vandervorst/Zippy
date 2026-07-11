; Term(Wrap1 h z) = F  and  Sub k (Wrap1 h z) = Guard (Eqi k h) z
; paths are finite key sequences
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(define-fun-rec append ((p Path) (q Path)) Path
  (match p ((nil q) ((cons h t) (cons h (append t q))))))
; prefix r of p
(define-fun-rec isPrefix ((r Path) (p Path)) Bool
  (match r ((nil true)
            ((cons h t) (match p ((nil false)
                                  ((cons h2 t2) (and (= h h2) (isPrefix t t2)))))))))
(declare-fun Zs (Path) Bool)
(declare-const k Int) (declare-const h Int)
(define-fun inWrap ((p Path)) Bool (exists ((q Path)) (and (= p (cons h q)) (Zs q))))
(assert (not (and
  (= (inWrap nil) false)                                            ; Term rule
  (forall ((p Path)) (= (inWrap (cons k p)) (and (= k h) (Zs p)))) ; Sub rule
)))
(check-sat)
