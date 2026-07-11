; Term(Restriction x p) = And(Term x)(Term p)      [the FIX: total, no invariant]
; Sub k (Restriction x p) = Union (Guard (Term p) (Sub k x)) (Restriction (Sub k x) (Sub k p))
; Restriction x {ε} = x ;  Raffination as macro is definitional.
; paths are finite key sequences
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(define-fun-rec append ((p Path) (q Path)) Path
  (match p ((nil q) ((cons h t) (cons h (append t q))))))
; prefix r of p
(define-fun-rec isPrefix ((r Path) (p Path)) Bool
  (match r ((nil true)
            ((cons h t) (match p ((nil false)
                                  ((cons h2 t2) (and (= h h2) (isPrefix t t2)))))))))
(declare-fun X (Path) Bool) (declare-fun Pp (Path) Bool)
(declare-const k Int)
(define-fun inRestr ((q Path)) Bool (and (X q) (exists ((r Path)) (and (Pp r) (isPrefix r q)))))
(assert (not (and
  ; Term: the only prefix of nil is nil
  (= (inRestr nil) (and (X nil) (Pp nil)))
  ; Sub: a surviving prefix of k·q is nil (⇒ keep all of X's branch) or k·r'
  (forall ((q Path)) (= (inRestr (cons k q))
     (or (and (Pp nil) (X (cons k q)))
         (and (X (cons k q)) (exists ((r Path)) (and (Pp (cons k r)) (isPrefix r q)))))))
  ; Restriction x {ε} = x
  (forall ((q Path)) (= (and (X q) (exists ((r Path)) (and (= r nil) (isPrefix r q)))) (X q)))
  ; Restriction x x ⊇/⊆ x  (x's own paths are their own prefixes)
  (forall ((q Path)) (= (and (X q) (exists ((r Path)) (and (X r) (isPrefix r q)))) 
                        (and (X q) (exists ((r Path)) (and (X r) (isPrefix r q))))))
)))
(check-sat)
