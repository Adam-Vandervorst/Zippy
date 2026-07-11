; LEG B (tails-union): the EAGER TRIE union-fold over a complete key list = ∃h. h·p ∈ Z.
; (Leg A — the zipper key-fold — is keyfolds.smt2, already certified.)  Induction over the list.
; paths are finite key sequences
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(define-fun-rec append ((p Path) (q Path)) Path
  (match p ((nil q) ((cons h t) (cons h (append t q))))))
; prefix r of p
(define-fun-rec isPrefix ((r Path) (p Path)) Bool
  (match r ((nil true)
            ((cons h t) (match p ((nil false)
                                  ((cons h2 t2) (and (= h h2) (isPrefix t t2)))))))))
(declare-sort Trie 0)
(declare-fun term (Trie) Bool)
(declare-fun child (Trie Int) Trie)
(define-fun-rec mem ((t Trie) (p Path)) Bool
  (match p ((nil (term t)) ((cons k q) (mem (child t k) q)))))
(declare-fun u (Trie Trie) Trie)
(assert (forall ((a Trie) (b Trie) (p Path)) (= (mem (u a b) p) (or (mem a p) (mem b p)))))   ; certified: impl_union
(declare-fun g (Bool Trie) Trie)
(assert (forall ((c Bool) (t Trie) (p Path)) (= (mem (g c t) p) (and c (mem t p)))))          ; one-unfold lemma
(declare-datatypes ((KList 0)) (((knil) (kcons (khd Int) (ktl KList)))))
(declare-fun Z () Trie)
(define-fun-rec inK ((h Int) (ks KList)) Bool
  (match ks ((knil false) ((kcons j r) (or (= h j) (inK h r))))))
(declare-fun emp () Trie)
(assert (forall ((p Path)) (not (mem emp p))))
(declare-fun tf (KList) Trie)
(assert (= (tf knil) emp))
(assert (forall ((j Int) (r KList)) (= (tf (kcons j r)) (u (child Z j) (tf r)))))
(define-fun PF ((ks KList)) Bool (forall ((p Path))
  (= (mem (tf ks) p) (exists ((h Int)) (and (inK h ks) (mem (child Z h) p))))))
(assert (=> (and (PF knil) (forall ((j Int) (r KList)) (=> (PF r) (PF (kcons j r))))) (forall ((ks KList)) (PF ks))))
(declare-fun KS () KList)
(assert (forall ((h Int)) (=> (exists ((p Path)) (mem (child Z h) p)) (inK h KS))))
(assert (not (and (forall ((ks KList)) (PF ks))
                  (forall ((p Path)) (= (mem (tf KS) p) (exists ((h Int)) (mem (child Z h) p)))))))
(check-sat)
