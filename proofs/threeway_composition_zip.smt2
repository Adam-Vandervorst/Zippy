; LEG A (composition): ZIPPER observation = SET-OF-PATHS denotation, ∀ operands ∀ paths.
; Uses the certified composition movement rule (composition.smt2) as a lemma; induction on p.
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
(define-fun den ((a Trie) (b Trie) (p Path)) Bool
  (exists ((q Path) (r Path)) (and (= p (append q r)) (mem a q) (mem b r))))
; the CERTIFIED movement rule for composition (composition.smt2), instantiated at mem:
(assert (forall ((a Trie) (b Trie)) (= (den a b nil) (and (term a) (term b)))))
(assert (forall ((a Trie) (b Trie) (k Int) (p Path))
  (= (den a b (cons k p))
     (or (den (child a k) b p) (and (term a) (mem (child b k) p))))))
(define-fun-rec zc ((a Trie) (b Trie) (p Path)) Bool
  (match p ((nil (and (term a) (term b)))
            ((cons k q) (or (zc (child a k) b q) (and (term a) (mem (child b k) q)))))))
(define-fun PP ((p Path)) Bool (forall ((a Trie) (b Trie)) (= (zc a b p) (den a b p))))
(assert (=> (and (PP nil) (forall ((k Int) (q Path)) (=> (PP q) (PP (cons k q))))) (forall ((p Path)) (PP p))))
(assert (not (forall ((p Path)) (PP p))))
(check-sat)
