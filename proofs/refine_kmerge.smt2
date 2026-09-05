; LIST REFINEMENT (KMerge): the sorted-merge RULES (the three guarded egg rewrites) implement set
; union on key lists:  inK(h, merge(a,b)) ⟺ inK(h,a) ∨ inK(h,b).
; Pair recursion: nested structural-induction schemata (outer on a; inner on b with the outer
; hypothesis available) — vampire/z3 discharge the instantiated schemata in FOL.
(declare-datatypes ((KList 0)) (((knil) (kcons (khd Int) (ktl KList)))))
(declare-fun inK (Int KList) Bool)
(assert (forall ((h Int)) (= (inK h knil) false)))
(assert (forall ((h Int) (j Int) (r KList)) (= (inK h (kcons j r)) (or (= h j) (inK h r)))))
(declare-fun merge (KList KList) KList)
(assert (forall ((b KList)) (= (merge knil b) b)))
(assert (forall ((a KList)) (= (merge a knil) a)))
(assert (forall ((k1 Int) (r1 KList) (k2 Int) (r2 KList))
  (=> (< k1 k2) (= (merge (kcons k1 r1) (kcons k2 r2)) (kcons k1 (merge r1 (kcons k2 r2)))))))
(assert (forall ((k1 Int) (r1 KList) (k2 Int) (r2 KList))
  (=> (< k2 k1) (= (merge (kcons k1 r1) (kcons k2 r2)) (kcons k2 (merge (kcons k1 r1) r2))))))
(assert (forall ((k1 Int) (r1 KList) (k2 Int) (r2 KList))
  (=> (= k1 k2) (= (merge (kcons k1 r1) (kcons k2 r2)) (kcons k1 (merge r1 r2))))))
(define-fun Q ((a KList) (b KList)) Bool
  (forall ((h Int)) (= (inK h (merge a b)) (or (inK h a) (inK h b)))))
(define-fun P ((a KList)) Bool (forall ((b KList)) (Q a b)))
; inner schema: for any fixed head/tail with P(tail) and P instances below, Q(kcons k1 r1, ·) ∀b
(assert (forall ((k1 Int) (r1 KList))
  (=> (and (P r1)
           (Q (kcons k1 r1) knil)
           (forall ((k2 Int) (r2 KList)) (=> (Q (kcons k1 r1) r2) (Q (kcons k1 r1) (kcons k2 r2)))))
      (P (kcons k1 r1)))))
; outer schema
; ASSUMED: T1
(assert (=> (and (P knil) (forall ((k1 Int) (r1 KList)) (=> (P r1) (P (kcons k1 r1)))))
            (forall ((a KList)) (P a))))
(assert (not (forall ((a KList) (b KList)) (Q a b))))
(check-sat)
