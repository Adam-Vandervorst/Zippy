; LEG A (restriction): ZIPPER observation = SET-OF-PATHS denotation (TOTAL semantics).
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
(define-fun den ((x Trie) (pp Trie) (p Path)) Bool
  (and (mem x p) (exists ((r Path)) (and (mem pp r) (isPrefix r p)))))
; the CERTIFIED movement rule for restriction (restriction.smt2), instantiated at mem:
(assert (forall ((x Trie) (pp Trie)) (= (den x pp nil) (and (term x) (term pp)))))
(assert (forall ((x Trie) (pp Trie) (k Int) (p Path))
  (= (den x pp (cons k p))
     (or (and (term pp) (mem (child x k) p)) (den (child x k) (child pp k) p)))))
(define-fun-rec zr ((x Trie) (pp Trie) (p Path)) Bool
  (match p ((nil (and (term x) (term pp)))
            ((cons k q) (or (and (term pp) (mem (child x k) q)) (zr (child x k) (child pp k) q))))))
(define-fun PP ((p Path)) Bool (forall ((x Trie) (pp Trie)) (= (zr x pp p) (den x pp p))))
(assert (=> (and (PP nil) (forall ((k Int) (q Path)) (=> (PP q) (PP (cons k q))))) (forall ((p Path)) (PP p))))
(assert (not (forall ((p Path)) (PP p))))
(check-sat)
