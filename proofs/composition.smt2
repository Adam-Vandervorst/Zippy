; Term(Composition a b) = And(Term a)(Term b)   and
; Sub k (Composition a b) = Union (Composition (Sub k a) b) (Guard (Term a) (Sub k b)).
; Uses lemma_append_cons.smt2 (z3: unsat) as an assumption.
; paths are finite key sequences
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(define-fun-rec append ((p Path) (q Path)) Path
  (match p ((nil q) ((cons h t) (cons h (append t q))))))
; prefix r of p
(define-fun-rec isPrefix ((r Path) (p Path)) Bool
  (match r ((nil true)
            ((cons h t) (match p ((nil false)
                                  ((cons h2 t2) (and (= h h2) (isPrefix t t2)))))))))
(declare-fun A (Path) Bool) (declare-fun B (Path) Bool)
(declare-const k Int)
(define-fun inComp ((p Path)) Bool
  (exists ((q Path) (r Path)) (and (= p (append q r)) (A q) (B r))))
(assert (forall ((k2 Int) (p Path) (q Path) (r Path))
  (= (= (cons k2 p) (append q r))
     (or (and (= q nil) (= r (cons k2 p)))
         (exists ((q2 Path)) (and (= q (cons k2 q2)) (= p (append q2 r))))))))
(assert (not (and
  (= (inComp nil) (and (A nil) (B nil)))
  (forall ((p Path)) (= (inComp (cons k p))
     (or (exists ((q Path) (r Path)) (and (= p (append q r)) (A (cons k q)) (B r)))
         (and (A nil) (B (cons k p))))))
)))
(check-sat)
