; THE DATALOG JOIN SPECIFICATION — the one place the workload's semantics was previously
; axiom-only.  For binary relations E, S (sets of 2-item paths):
;   p ∈ join(E,S) ⟺ ∃a,b,c.  a·b ∈ E  ∧  b·c ∈ S  ∧  p = a·c
; The implementation under proof is JoinBody's App rule composed with the per-head iteration:
;   App (JoinBody S) h t  =  Wrap1 h (TailsUnion (Restriction S t))     with t = Sub h E,
; i.e.  Bd(h, p)  ⟺  ∃c. p = h·c ∧ ∃b. E(h·b) ∧ S(b·c)
; (Restriction keeps S-paths with a prefix among the h-tails of E — for 2-item paths the prefix is
; the middle item b; TailsUnion drops it; Wrap1 restores the head) — and the iteration over the
; EXACT keys of E (keyfold_iter.smt2) unions Bd over present heads.  Theorem: that union IS join.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-fun E (Path) Bool) (declare-fun S (Path) Bool)
; binary-relation shape: members are exactly 2-item paths
(assert (forall ((p Path)) (=> (E p) (exists ((a Int) (b Int)) (= p (cons a (cons b nil)))))))
(assert (forall ((p Path)) (=> (S p) (exists ((b Int) (c Int)) (= p (cons b (cons c nil)))))))
(define-fun joinSpec ((p Path)) Bool
  (exists ((a Int) (b Int) (c Int))
    (and (E (cons a (cons b nil))) (S (cons b (cons c nil))) (= p (cons a (cons c nil))))))
; the implemented body denotation (as derived from App/Restriction/TailsUnion/Wrap1 semantics)
(define-fun Bd ((h Int) (p Path)) Bool
  (exists ((c Int)) (and (= p (cons h (cons c nil)))
    (exists ((b Int)) (and (E (cons h (cons b nil))) (S (cons b (cons c nil))))))))
(define-fun present ((h Int)) Bool (exists ((q Path)) (E (cons h q))))
; iterating Bd over the present heads of E (the proved fold) = the join specification
(assert (not (forall ((p Path))
  (= (exists ((h Int)) (and (present h) (Bd h p))) (joinSpec p)))))
(check-sat)
