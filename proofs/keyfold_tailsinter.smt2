; TAILS-INTERSECTION FOLD: with an EXACT key list (SOUND: every listed key is present — a spurious
; empty-subspace key would poison the meet, per zipper.egg's own header — and COMPLETE: every
; present key is listed), KFoldI computes the tails-intersection denotation
;   p ∈ tails∩(Z) ⟺ (∃h. present h) ∧ (∀h. present h ⇒ Z(h·p))
; by induction over the key list.  Note the empty/singleton conventions: fold of [] = ∅ (the
; denotation is empty when no head exists), fold of [h] = Sub h Z.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-datatypes ((KList 0)) (((knil) (kcons (khd Int) (ktl KList)))))
(declare-fun Z (Path) Bool)
(define-fun present ((h Int)) Bool (exists ((q Path)) (Z (cons h q))))
(declare-fun inK (Int KList) Bool)
(assert (forall ((h Int)) (= (inK h knil) false)))
(assert (forall ((h Int) (j Int) (r KList)) (= (inK h (kcons j r)) (or (= h j) (inK h r)))))
(declare-fun foldI (KList Path) Bool)
(assert (forall ((p Path)) (= (foldI knil p) false)))
(assert (forall ((h Int) (p Path)) (= (foldI (kcons h knil) p) (Z (cons h p)))))
(assert (forall ((h Int) (j Int) (r KList) (p Path))
  (= (foldI (kcons h (kcons j r)) p) (and (Z (cons h p)) (foldI (kcons j r) p)))))
; the key list KS: sound and complete
(declare-fun KS () KList)
(assert (forall ((h Int)) (=> (inK h KS) (present h))))            ; SOUND
(assert (forall ((h Int)) (=> (present h) (inK h KS))))            ; COMPLETE
; induction over ks: fold(ks,p) ⟺ ks=[] ? false : ∀h∈ks. Z(h·p)   (for SOUND lists)
(define-fun PF ((ks KList)) Bool (forall ((p Path))
  (= (foldI ks p) (and (not (= ks knil)) (forall ((h Int)) (=> (inK h ks) (Z (cons h p))))))))
(assert (=> (and (PF knil) (forall ((j Int) (r KList)) (=> (PF r) (PF (kcons j r))))) (forall ((ks KList)) (PF ks))))
(assert (not
  (forall ((p Path)) (= (foldI KS p)
     (and (exists ((h Int)) (present h)) (forall ((h Int)) (=> (present h) (Z (cons h p)))))))))
(check-sat)
