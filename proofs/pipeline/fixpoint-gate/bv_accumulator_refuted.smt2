; (ii) the pre-fix accumulator answer {a,b} is INCONSISTENT with the axioms.  Expected: unsat.
; This is the decisive form of the differential: not `we cannot prove {a,b}`, but `{a,b} is
; refuted`.  It fails the moment an executor goes back to iterating F alone.
; DECIDABLE TWIN of the fixpoint_is_lfp.smt2:47-50 counterexample.  A set over {a,b,c} is a
; 3-bit vector (bit0=a, bit1=b, bit2=c); `subset x y` is `x|y = y`.  EVERYTHING here is
; decidable and quantifier-free apart from one bounded ∀ over BitVec 3, so a `sat` answer
; comes with a MODEL and an `unsat` answer is a refutation — no timeouts, no `unknown`.
;
;   F(X) = {b if a∈X} ∪ {c if a∈X and b∈X}          init = {a}
;
; F is MONOTONE and NOT inflationary at init, which is exactly the configuration in which
; monotonicity alone fails to make an iteration reach the least post-fixpoint.
(define-fun sub ((x (_ BitVec 3)) (y (_ BitVec 3))) Bool (= (bvor x y) y))
(define-fun hasA ((x (_ BitVec 3))) Bool (= (bvand x #b001) #b001))
(define-fun hasB ((x (_ BitVec 3))) Bool (= (bvand x #b010) #b010))
(define-fun F ((x (_ BitVec 3))) (_ BitVec 3)
  (bvor (ite (hasA x) #b010 #b000) (ite (and (hasA x) (hasB x)) #b100 #b000)))
(define-fun init () (_ BitVec 3) #b001)
(declare-const fx (_ BitVec 3))
; the two POST-FIXPOINT axioms the emitter writes (AgSmt.fixSym)
(assert (sub init fx))
(assert (sub (F fx) fx))
; PARK INDUCTION, with the candidate UNIVERSALLY quantified — so `least` really is least
(assert (forall ((y (_ BitVec 3))) (=> (and (sub init y) (sub (F y) y)) (sub fx y))))
(assert (= fx #b011))         ; the PRE-FIX executors' answer {a,b}
(check-sat)
