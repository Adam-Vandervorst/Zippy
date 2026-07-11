; FOLD RULE CERTIFICATION.  Given an EXACT key list for z at the focus —
;   sound:    every listed key has a non-empty subspace       (not needed for tails∪)
;   complete: every key with a non-empty subspace is listed
; the fold rules compute the right set:
;   TailsUnion z = KFoldU ks z :   p ∈ ⋃_h Sub h z  ⟺  ∃h∈ks. p ∈ Sub h z
; proved by induction on ks (explicit schema instance).  (tails∩/Head/Iter have the same shape;
; tails∪ is the load-bearing one for the datalog workload and is the one proved here.)
; paths are finite key sequences
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(define-fun-rec append ((p Path) (q Path)) Path
  (match p ((nil q) ((cons h t) (cons h (append t q))))))
; prefix r of p
(define-fun-rec isPrefix ((r Path) (p Path)) Bool
  (match r ((nil true)
            ((cons h t) (match p ((nil false)
                                  ((cons h2 t2) (and (= h h2) (isPrefix t t2)))))))))
(declare-datatypes ((KList 0)) (((knil) (kcons (khd Int) (ktl KList)))))
(declare-fun Zm (Int Path) Bool)              ; Zm h p  ⟺  p ∈ Sub h z  (z fixed, uninterpreted)
(define-fun-rec inK ((h Int) (ks KList)) Bool
  (match ks ((knil false) ((kcons j r) (or (= h j) (inK h r))))))
(define-fun-rec inFoldU ((ks KList) (p Path)) Bool
  (match ks ((knil false) ((kcons j r) (or (Zm j p) (inFoldU r p))))))
; goal: ∀ks p. inFoldU ks p ⟺ ∃h. inK h ks ∧ Zm h p    — induction on ks
(define-fun PF ((ks KList)) Bool (forall ((p Path)) (= (inFoldU ks p) (exists ((h Int)) (and (inK h ks) (Zm h p))))))
(assert (=> (and (PF knil) (forall ((j Int) (r KList)) (=> (PF r) (PF (kcons j r))))) (forall ((ks KList)) (PF ks))))
; completeness of exact keys closes the gap to "∃h (any h). p ∈ Sub h z":
(declare-fun KS () KList)
(assert (forall ((h Int)) (=> (exists ((p Path)) (Zm h p)) (inK h KS))))   ; complete
(assert (not (and
  (forall ((ks KList)) (PF ks))
  (forall ((p Path)) (= (inFoldU KS p) (exists ((h Int)) (Zm h p)))))))
(check-sat)
