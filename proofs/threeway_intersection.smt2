; THREE-WAY EQUIVALENCE (intersection): the ZIPPER observation, the SET-OF-PATHS denotation, and the EAGER
; TRIE recursion agree ∀ operand tries ∀ paths.  zipobs mirrors the movement rules (Sub pushes the
; same key into both operands, Term is the combinator); the trie op is its recursion equations; the
; set-of-paths denotation is the pointwise formula.  Explicit structural induction on the path.
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
; ZIPPER observation of the virtual intersection cursor, following the movement rules verbatim
(define-fun-rec zipobs ((a Trie) (b Trie) (p Path)) Bool
  (match p ((nil (and (term a) (term b)))
            ((cons k q) (zipobs (child a k) (child b k) q)))))
; EAGER trie op by its recursion equations
(declare-fun f (Trie Trie) Trie)
(assert (forall ((a Trie) (b Trie)) (= (term (f a b)) (and (term a) (term b)))))
(assert (forall ((a Trie) (b Trie) (k Int)) (= (child (f a b) k) (f (child a k) (child b k)))))
; the chain, ∀p by explicit induction: zipobs = SET-OF-PATHS pointwise denotation = mem(f a b)
(define-fun PP ((p Path)) Bool (forall ((a Trie) (b Trie))
  (and (= (zipobs a b p) (and (mem a p) (mem b p)))          ; zipper = set of paths
       (= (mem (f a b) p) (and (mem a p) (mem b p))))))      ; eager trie = set of paths
; ASSUMED: T1
(assert (=> (and (PP nil) (forall ((k Int) (q Path)) (=> (PP q) (PP (cons k q))))) (forall ((p Path)) (PP p))))
(assert (not (forall ((p Path)) (PP p))))
(check-sat)
