; LEG B (composition): the EAGER TRIE recursion computes the ZIPPER observation, ∀ operands ∀ paths
; — identical step shapes; with leg A (threeway_composition_zip.smt2: zipper = set-of-paths
; denotation, PROVED) the three-way chain closes by transitivity.  Fully first-order encoding.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-sort Trie 0)
(declare-fun term (Trie) Bool)
(declare-fun child (Trie Int) Trie)
(declare-fun mem (Trie Path) Bool)
(assert (forall ((t Trie)) (= (mem t nil) (term t))))
(assert (forall ((t Trie) (k Int) (q Path)) (= (mem t (cons k q)) (mem (child t k) q))))
(declare-fun u (Trie Trie) Trie)
(assert (forall ((a Trie) (b Trie) (p Path)) (= (mem (u a b) p) (or (mem a p) (mem b p)))))   ; certified: impl_union
(declare-fun g (Bool Trie) Trie)
(assert (forall ((c Bool) (t Trie) (p Path)) (= (mem (g c t) p) (and c (mem t p)))))
(declare-fun zc (Trie Trie Path) Bool)
(assert (forall ((a Trie) (b Trie)) (= (zc a b nil) (and (term a) (term b)))))
(assert (forall ((a Trie) (b Trie) (k Int) (q Path))
  (= (zc a b (cons k q)) (or (zc (child a k) b q) (and (term a) (mem (child b k) q))))))
(declare-fun tc (Trie Trie) Trie)
(assert (forall ((a Trie) (b Trie)) (= (term (tc a b)) (and (term a) (term b)))))
(assert (forall ((a Trie) (b Trie) (k Int))
  (= (child (tc a b) k) (u (tc (child a k) b) (g (term a) (child b k))))))
(define-fun PP ((p Path)) Bool (forall ((a Trie) (b Trie)) (= (mem (tc a b) p) (zc a b p))))
; ASSUMED: T1
(assert (=> (and (PP nil) (forall ((k Int) (q Path)) (=> (PP q) (PP (cons k q))))) (forall ((p Path)) (PP p))))
(assert (not (forall ((p Path)) (PP p))))
(check-sat)
