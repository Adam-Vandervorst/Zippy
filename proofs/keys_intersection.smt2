; KEYS CANDIDATE COMPLETENESS (∩): every present key of A∩B is in KInter(Keys A, Keys B)'s
; candidate set — h present in the intersection ⇒ h present in BOTH operands.  With KFilt
; (keep h iff Sub h nonempty ⟺ h present) exactness follows: Keys(A∩B) = the present keys.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-fun append (Path Path) Path)
(assert (forall ((q Path)) (= (append nil q) q)))
(assert (forall ((h Int) (t Path) (q Path)) (= (append (cons h t) q) (cons h (append t q)))))
(assert (forall ((k2 Int) (p Path) (q Path) (r Path))
  (= (= (cons k2 p) (append q r))
     (or (and (= q nil) (= r (cons k2 p)))
         (exists ((q2 Path)) (and (= q (cons k2 q2)) (= p (append q2 r))))))))
(declare-fun A (Path) Bool) (declare-fun B (Path) Bool)
(define-fun presentA ((h Int)) Bool (exists ((q Path)) (A (cons h q))))
(define-fun presentB ((h Int)) Bool (exists ((q Path)) (B (cons h q))))
(assert (not (forall ((h Int))
  (=> (exists ((q Path)) (and (A (cons h q)) (B (cons h q))))
      (and (presentA h) (presentB h))))))
(check-sat)
