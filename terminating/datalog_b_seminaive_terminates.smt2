; SMT-LIB twin of datalog_b_seminaive_terminates.p — termination of the three semi-naive MORKL
; Datalog programs (tc_sn / rsg_sn / pt_sn) via the lexicographic measure
;   mu(all, delta) = 2 * card(top \ all) + [delta != empty]
; The delta-consequence operator d stays FULLY UNINTERPRETED (no monotonicity needed), so this
; one theorem covers every semi-naive program with the shared transition
;   all' = all u (d(delta) \ all),  delta' = d(delta) \ all.
; Stepping-stone lemmas are re-proved from the base axioms in
; datalog_b_seminaive_lemmas.smt2 (z3), and bounded_growth_decrease in its own twin; both are
; asserted here as premises, mirroring the .p file's lemma-role imports.
(declare-sort Node 0)
(declare-sort NSet 0)
(declare-fun mem (Node NSet) Bool)
(declare-fun subset (NSet NSet) Bool)
(declare-fun card (NSet) Int)
(declare-fun setminus (NSet NSet) NSet)
(declare-fun cup (NSet NSet) NSet)
(declare-const empty NSet)
(declare-const top NSet)
(declare-fun flag (NSet) Int)
(declare-fun d (NSet) NSet)
(declare-fun allp (NSet NSet) NSet)
(declare-fun deltap (NSet NSet) NSet)
(declare-fun mu (NSet NSet) Int)
(assert (forall ((x Node) (a NSet) (b NSet))
  (= (mem x (cup a b)) (or (mem x a) (mem x b)))))
(assert (forall ((x Node) (a NSet) (b NSet))
  (= (mem x (setminus a b)) (and (mem x a) (not (mem x b))))))
(assert (forall ((a NSet) (b NSet))
  (= (subset a b) (forall ((x Node)) (=> (mem x a) (mem x b))))))
(assert (forall ((a NSet) (b NSet))
  (=> (forall ((x Node)) (= (mem x a) (mem x b))) (= a b))))
(assert (forall ((x Node)) (not (mem x empty))))
(assert (forall ((x Node)) (mem x top)))
(assert (forall ((a NSet)) (>= (card a) 0)))
(assert (= (flag empty) 0))
(assert (forall ((a NSet)) (=> (distinct a empty) (= (flag a) 1))))
; the shared semi-naive transition and its measure
(assert (forall ((a NSet) (dl NSet)) (= (allp a dl) (cup a (setminus (d dl) a)))))
(assert (forall ((a NSet) (dl NSet)) (= (deltap a dl) (setminus (d dl) a))))
(assert (forall ((a NSet) (dl NSet))
  (= (mu a dl) (+ (* 2 (card (setminus top a))) (flag dl)))))
; stepping stones (re-proved from the axioms above in datalog_b_seminaive_lemmas.smt2)
(assert (forall ((a NSet) (dl NSet)) (subset a (allp a dl))))
(assert (forall ((a NSet) (dl NSet)) (subset (allp a dl) top)))
(assert (forall ((a NSet) (dl NSet)) (=> (= (allp a dl) a) (= (deltap a dl) empty))))
(assert (forall ((a NSet)) (and (>= (flag a) 0) (<= (flag a) 1))))
; proved in bounded_growth_decrease.smt2 (and .p), imported as a premise
(assert (forall ((r NSet) (s NSet) (u NSet))
  (=> (and (subset r s) (subset s u) (distinct s r))
      (< (card (setminus u s)) (card (setminus u r))))))
; the theorem: mu maps states into the naturals and strictly decreases on every
; state-changing step, for EVERY delta-consequence operator d
(assert (not (forall ((a NSet) (dl NSet))
  (and (>= (mu a dl) 0)
       (=> (or (distinct (allp a dl) a) (distinct (deltap a dl) dl))
           (< (mu (allp a dl) (deltap a dl)) (mu a dl)))))))
(check-sat)
