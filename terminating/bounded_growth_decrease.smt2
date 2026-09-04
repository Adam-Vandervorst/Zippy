; SMT-LIB twin of bounded_growth_decrease.p (mechanical TFF->SMT translation) — the core
; measure lemma: strict growth inside a finite universe strictly shrinks the complement.
;   subset(R,S) & subset(S,U) & S != R  =>  card(U\S) < card(U\R)
(declare-sort Node 0)
(declare-sort NSet 0)
(declare-fun mem (Node NSet) Bool)
(declare-fun subset (NSet NSet) Bool)
(declare-fun card (NSet) Int)
(declare-fun setminus (NSet NSet) NSet)
(assert (forall ((x Node) (a NSet) (b NSet))
  (= (mem x (setminus a b)) (and (mem x a) (not (mem x b))))))
(assert (forall ((a NSet) (b NSet))
  (= (subset a b) (forall ((x Node)) (=> (mem x a) (mem x b))))))
(assert (forall ((a NSet) (b NSet))
  (=> (forall ((x Node)) (= (mem x a) (mem x b))) (= a b))))
; ASSUMED: T7
(assert (forall ((a NSet)) (>= (card a) 0)))
; ASSUMED: T7
(assert (forall ((a NSet) (b NSet) (w Node))
  (=> (and (subset a b) (mem w b) (not (mem w a))) (< (card a) (card b)))))
(assert (not (forall ((r NSet) (s NSet) (u NSet))
  (=> (and (subset r s) (subset s u) (distinct s r))
      (< (card (setminus u s)) (card (setminus u r)))))))
(check-sat)
