; KFILT EXACTNESS (set level): filtering any COMPLETE candidate set by subspace non-emptiness
; yields exactly the present keys — h kept ⟺ h candidate ∧ Sub h X nonempty; with completeness
; (present ⇒ candidate) and Sub h X nonempty ⟺ h present, kept ⟺ present.
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
(declare-fun cand (Int) Bool)
; PREMISE: every present head is a candidate (the exact-key filter's side condition)
(assert (forall ((h Int)) (=> (presentA h) (cand h))))            ; completeness hypothesis
(define-fun kept ((h Int)) Bool (and (cand h) (exists ((q Path)) (A (cons h q)))))
(assert (not (forall ((h Int)) (= (kept h) (presentA h)))))
(check-sat)
