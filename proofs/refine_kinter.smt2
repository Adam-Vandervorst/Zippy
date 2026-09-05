; LIST REFINEMENT (KInter): the sorted-intersect rules implement set intersection on key lists,
; GIVEN SORTEDNESS (strictly ascending) of both inputs — the guards skip by <, which is only
; complete when smaller keys cannot recur later.  inK(h, inter(a,b)) ⟺ inK(h,a) ∧ inK(h,b).
(declare-datatypes ((KList 0)) (((knil) (kcons (khd Int) (ktl KList)))))
(declare-fun inK (Int KList) Bool)
(assert (forall ((h Int)) (= (inK h knil) false)))
(assert (forall ((h Int) (j Int) (r KList)) (= (inK h (kcons j r)) (or (= h j) (inK h r)))))
(declare-fun lbnd (Int KList) Bool)                    ; lo < every key of l
(assert (forall ((lo Int)) (lbnd lo knil)))
(assert (forall ((lo Int) (j Int) (r KList)) (= (lbnd lo (kcons j r)) (and (< lo j) (lbnd j r)))))
(declare-fun srt (KList) Bool)
(assert (= (srt knil) true))
(assert (forall ((j Int) (r KList)) (= (srt (kcons j r)) (and (lbnd j r) (srt r)))))
(declare-fun inter (KList KList) KList)
(assert (forall ((b KList)) (= (inter knil b) knil)))
(assert (forall ((a KList)) (= (inter a knil) knil)))
(assert (forall ((k1 Int) (r1 KList) (k2 Int) (r2 KList))
  (=> (< k1 k2) (= (inter (kcons k1 r1) (kcons k2 r2)) (inter r1 (kcons k2 r2))))))
(assert (forall ((k1 Int) (r1 KList) (k2 Int) (r2 KList))
  (=> (< k2 k1) (= (inter (kcons k1 r1) (kcons k2 r2)) (inter (kcons k1 r1) r2)))))
(assert (forall ((k1 Int) (r1 KList) (k2 Int) (r2 KList))
  (=> (= k1 k2) (= (inter (kcons k1 r1) (kcons k2 r2)) (kcons k1 (inter r1 r2))))))
; the lower-bound lemma needed for guard completeness: lbnd lo l ⇒ ¬inK(lo', l) for lo' ≤ lo
(define-fun PL ((l KList)) Bool (forall ((lo Int) (h Int)) (=> (and (lbnd lo l) (<= h lo)) (not (inK h l)))))
; ASSUMED: T1
(assert (=> (and (PL knil) (forall ((j Int) (r KList)) (=> (PL r) (PL (kcons j r))))) (forall ((l KList)) (PL l))))
(define-fun Q ((a KList) (b KList)) Bool
  (=> (and (srt a) (srt b))
      (forall ((h Int)) (= (inK h (inter a b)) (and (inK h a) (inK h b))))))
(define-fun P ((a KList)) Bool (forall ((b KList)) (Q a b)))
(assert (forall ((k1 Int) (r1 KList))
  (=> (and (P r1)
           (Q (kcons k1 r1) knil)
           (forall ((k2 Int) (r2 KList)) (=> (and (Q (kcons k1 r1) r2) (Q r1 (kcons k2 r2)) (Q r1 r2)) (Q (kcons k1 r1) (kcons k2 r2)))))
      (P (kcons k1 r1)))))
; ASSUMED: T1
(assert (=> (and (P knil) (forall ((k1 Int) (r1 KList)) (=> (P r1) (P (kcons k1 r1)))))
            (forall ((a KList)) (P a))))
(assert (not (forall ((a KList) (b KList)) (Q a b))))
(check-sat)
