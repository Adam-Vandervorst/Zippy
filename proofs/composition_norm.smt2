; Composition(Wrap1 h a) b = Wrap1 h (Composition a b);  ε is the two-sided identity.
; Uses lemma_append_cons.smt2 and lemma_append_nil.smt2 (both z3: unsat) as assumptions.
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
(declare-const h Int)
(assert (forall ((k2 Int) (p Path) (q Path) (r Path))
  (= (= (cons k2 p) (append q r))
     (or (and (= q nil) (= r (cons k2 p)))
         (exists ((q2 Path)) (and (= q (cons k2 q2)) (= p (append q2 r))))))))
(assert (forall ((q Path)) (= (append q nil) q)))
(assert (not (and
  (forall ((p Path)) (= (exists ((q Path) (r Path)) (and (= p (append q r))
                                                          (exists ((q2 Path)) (and (= q (cons h q2)) (A q2))) (B r)))
                        (exists ((p2 Path)) (and (= p (cons h p2))
                          (exists ((q Path) (r Path)) (and (= p2 (append q r)) (A q) (B r)))))))
  (forall ((p Path)) (= (exists ((q Path) (r Path)) (and (= p (append q r)) (= q nil) (B r))) (B p)))
  (forall ((p Path)) (= (exists ((q Path) (r Path)) (and (= p (append q r)) (A q) (= r nil))) (A p)))
)))
(check-sat)
