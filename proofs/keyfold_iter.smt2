; ITER FOLD (head-dependent bodies): with an exact key list and an ARBITRARY body denotation
; Bd(h, p) (the defunctionalised App applied to head h and the h-tails), IFold computes
;   p ∈ Iter(Z, b) ⟺ ∃h. present(h) ∧ Bd(h, p)
; by induction over the key list.  Soundness of the list matters (a spurious head would invoke the
; body on an empty group); completeness matters (no group may be missed).
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-datatypes ((KList 0)) (((knil) (kcons (khd Int) (ktl KList)))))
(declare-fun Z (Path) Bool)
(define-fun present ((h Int)) Bool (exists ((q Path)) (Z (cons h q))))
(declare-fun inK (Int KList) Bool)
(assert (forall ((h Int)) (= (inK h knil) false)))
(assert (forall ((h Int) (j Int) (r KList)) (= (inK h (kcons j r)) (or (= h j) (inK h r)))))
(declare-fun KS () KList)
; DEFINITION
(assert (forall ((h Int)) (=> (inK h KS) (present h))))
; DEFINITION
(assert (forall ((h Int)) (=> (present h) (inK h KS))))
(declare-fun Bd (Int Path) Bool)
(declare-fun foldIt (KList Path) Bool)
(assert (forall ((p Path)) (= (foldIt knil p) false)))
(assert (forall ((h Int) (r KList) (p Path))
  (= (foldIt (kcons h r) p) (or (Bd h p) (foldIt r p)))))
(define-fun PF ((ks KList)) Bool (forall ((p Path))
  (= (foldIt ks p) (exists ((h Int)) (and (inK h ks) (Bd h p))))))
; ASSUMED: T1
(assert (=> (and (PF knil) (forall ((j Int) (r KList)) (=> (PF r) (PF (kcons j r))))) (forall ((ks KList)) (PF ks))))
(assert (not (forall ((p Path))
  (= (foldIt KS p) (exists ((h Int)) (and (present h) (Bd h p)))))))
(check-sat)
