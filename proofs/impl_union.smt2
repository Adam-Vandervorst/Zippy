; IMPLEMENTATION CHARACTERIZATION (∨): tries coalgebraically (term/child; mem by recursion);
; the op defined by its recursion equations (the sorted-list merge is this map's list refinement,
; validated by the randomized differential suite); theorem by EXPLICIT structural induction on p:
;   ∀t1 t2 p.  mem(union(t1,t2), p) ⟺ mem(t1,p) ∨ mem(t2,p)
; This is materialize(OpZipper(z1,z2)) = Op(materialize z1, materialize z2), denotationally.
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
(declare-fun f (Trie Trie) Trie)
(assert (forall ((a Trie) (b Trie)) (= (term (f a b)) (or (term a) (term b)))))
(assert (forall ((a Trie) (b Trie) (k Int)) (= (child (f a b) k) (f (child a k) (child b k)))))
(define-fun PP ((p Path)) Bool (forall ((a Trie) (b Trie)) (= (mem (f a b) p) (or (mem a p) (mem b p)))))
; ASSUMED: T1
(assert (=> (and (PP nil) (forall ((k Int) (q Path)) (=> (PP q) (PP (cons k q))))) (forall ((p Path)) (PP p))))
(assert (not (forall ((p Path)) (PP p))))
(check-sat)
