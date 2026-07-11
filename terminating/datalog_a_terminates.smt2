; SMT-LIB twin of datalog_a_terminates.p — termination of all six datalog_a.txt routines:
; step(R) = R u F(R) with F COMPLETELY UNINTERPRETED (no monotonicity used); the chain is
; inflationary by construction and growth pays down the finite budget card(top \ R).
; bounded_growth_decrease is imported as a premise (proved in bounded_growth_decrease.smt2).
(declare-sort Node 0)
(declare-sort NSet 0)
(declare-fun mem (Node NSet) Bool)
(declare-fun subset (NSet NSet) Bool)
(declare-fun card (NSet) Int)
(declare-fun setminus (NSet NSet) NSet)
(declare-fun cup (NSet NSet) NSet)
(declare-const top NSet)
(declare-fun f (NSet) NSet)
(assert (forall ((x Node) (a NSet) (b NSet))
  (= (mem x (cup a b)) (or (mem x a) (mem x b)))))
(assert (forall ((a NSet) (b NSet))
  (= (subset a b) (forall ((x Node)) (=> (mem x a) (mem x b))))))
(assert (forall ((x Node)) (mem x top)))
(assert (forall ((a NSet)) (>= (card a) 0)))
; proved in bounded_growth_decrease.smt2 (and .p), imported as a premise
(assert (forall ((r NSet) (s NSet) (u NSet))
  (=> (and (subset r s) (subset s u) (distinct s r))
      (< (card (setminus u s)) (card (setminus u r))))))
(assert (not (forall ((r NSet))
  (and (subset r (cup r (f r)))
       (=> (distinct (cup r (f r)) r)
           (< (card (setminus top (cup r (f r)))) (card (setminus top r))))))))
(check-sat)
