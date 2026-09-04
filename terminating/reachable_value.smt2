; SMT-LIB twin of reachable_value.p — value facts of the accumulated masked iteration:
;   iter(0) = {v0},  iter(n+1) = step(iter(n));  acc(0) = {v0},  acc(n+1) = acc(n) u iter(n+1)
; ⊢ ∀n≥0. v0 ∈ acc(n)  ∧  (v0 ∈ mask ⇒ acc(n) ⊆ mask).
; The induction over the naturals is an EXPLICIT schema instance (valid for n ≥ 0), same
; discipline as the structural-induction instances in proofs/laws/.
(declare-sort Node 0)
(declare-sort NSet 0)
(declare-fun mem (Node NSet) Bool)
(declare-fun subset (NSet NSet) Bool)
(declare-fun cup (NSet NSet) NSet)
(declare-fun sing (Node) NSet)
(declare-fun step (NSet) NSet)
(declare-const mask NSet)
(declare-const v0 Node)
(declare-fun iter (Int) NSet)
(declare-fun acc (Int) NSet)
(assert (forall ((a NSet)) (subset a a)))
(assert (forall ((a NSet) (b NSet) (c NSet))
  (=> (and (subset a b) (subset b c)) (subset a c))))
; DEFINITION
(assert (forall ((a NSet) (b NSet)) (subset a (cup a b))))
; DEFINITION
(assert (forall ((a NSet) (b NSet)) (subset b (cup a b))))
; DEFINITION
(assert (forall ((a NSet) (b NSet) (c NSet))
  (=> (and (subset a c) (subset b c)) (subset (cup a b) c))))
(assert (forall ((a NSet) (b NSet) (x Node))
  (=> (and (subset a b) (mem x a)) (mem x b))))
; DEFINITION
(assert (forall ((x Node)) (mem x (sing x))))
; DEFINITION
(assert (forall ((x Node) (b NSet)) (=> (mem x b) (subset (sing x) b))))
; PREMISE: one step stays inside the universe mask
(assert (forall ((r NSet)) (subset (step r) mask)))
(assert (= (iter 0) (sing v0)))
(assert (forall ((n Int)) (=> (>= n 0) (= (iter (+ n 1)) (step (iter n))))))
(assert (= (acc 0) (sing v0)))
(assert (forall ((n Int)) (=> (>= n 0) (= (acc (+ n 1)) (cup (acc n) (iter (+ n 1)))))))
; explicit induction schema instance over the naturals for
;   P(n) := v0 ∈ acc(n) ∧ (v0 ∈ mask ⇒ acc(n) ⊆ mask)
(define-fun P ((n Int)) Bool
  (and (mem v0 (acc n)) (=> (mem v0 mask) (subset (acc n) mask))))
; ASSUMED: T1
(assert (=> (and (P 0) (forall ((n Int)) (=> (and (>= n 0) (P n)) (P (+ n 1)))))
            (forall ((n Int)) (=> (>= n 0) (P n)))))
(assert (not (forall ((n Int)) (=> (>= n 0)
  (and (mem v0 (acc n)) (=> (mem v0 mask) (subset (acc n) mask)))))))
(check-sat)
