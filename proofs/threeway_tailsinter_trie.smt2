; LEG B (tails-intersection): the EAGER TRIE intersection-fold (ClTI) over a SOUND and COMPLETE
; key list = the tails-∩ semantics: p ∈ tails∩(Z) ⟺ (∃h. child h ≠ ∅) ∧ ∀h. child h ≠ ∅ → h·p ∈ Z.
; (Leg A — the zipper key-fold — is keyfold_tailsinter.smt2.)  UNLIKE tails-∪, soundness of the
; key list is LOAD-BEARING: one listed key with an empty child annihilates the fold.  The empty
; key list is the separate ClTI(CNil) = ∅ rule, matching the no-heads semantics.  Induction over
; the (nonempty) list is an explicit schema instance.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-sort Trie 0)
(declare-fun term (Trie) Bool)
(declare-fun child (Trie Int) Trie)
(define-fun-rec mem ((t Trie) (p Path)) Bool
  (match p ((nil (term t)) ((cons k q) (mem (child t k) q)))))
(declare-fun i (Trie Trie) Trie)
(assert (forall ((a Trie) (b Trie) (p Path)) (= (mem (i a b) p) (and (mem a p) (mem b p)))))   ; certified: impl_intersection
(declare-datatypes ((KList 0)) (((knil) (kcons (khd Int) (ktl KList)))))
(declare-fun Z () Trie)
(define-fun-rec inK ((h Int) (ks KList)) Bool
  (match ks ((knil false) ((kcons j r) (or (= h j) (inK h r))))))
; tif: the ClTI fold over a NONEMPTY key list (the CNil case is the separate ∅ rule)
(declare-fun tif (KList) Trie)
(assert (forall ((j Int)) (= (tif (kcons j knil)) (child Z j))))
(assert (forall ((j Int) (j2 Int) (r KList))
  (= (tif (kcons j (kcons j2 r))) (i (child Z j) (tif (kcons j2 r))))))
; induction over the tail list: P(r) := ∀j p. mem (tif (j :: r)) p ⟺ h·p ∈ Z for all h ∈ j :: r
(define-fun P ((r KList)) Bool (forall ((j Int) (p Path))
  (= (mem (tif (kcons j r)) p)
     (and (mem (child Z j) p) (forall ((h Int)) (=> (inK h r) (mem (child Z h) p)))))))
(assert (=> (and (P knil) (forall ((j2 Int) (r KList)) (=> (P r) (P (kcons j2 r)))))
            (forall ((r KList)) (P r))))                     ; explicit schema instance (valid for KList)
; KS: SOUND (every listed child nonempty) and COMPLETE (every nonempty child listed), NONEMPTY
(declare-fun KS () KList)
(declare-const k0 Int)
(declare-fun KR () KList)
(assert (= KS (kcons k0 KR)))
(assert (forall ((h Int)) (=> (inK h KS) (exists ((p Path)) (mem (child Z h) p)))))
(assert (forall ((h Int)) (=> (exists ((p Path)) (mem (child Z h) p)) (inK h KS))))
(assert (not (and (forall ((r KList)) (P r))
                  (forall ((p Path))
                    (= (mem (tif KS) p)
                       (and (exists ((h Int) (q Path)) (mem (child Z h) q))
                            (forall ((h Int)) (=> (exists ((q Path)) (mem (child Z h) q))
                                                  (mem (child Z h) p)))))))))
(check-sat)
