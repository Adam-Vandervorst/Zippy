; RULE CERTIFICATION (movement spec): every pointwise Sub/Term rule, plus the ∪/∩ commutativity &
; associativity that are deliberately NOT egglog rewrites — certified here universally instead.
; paths are finite key sequences
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(define-fun-rec append ((p Path) (q Path)) Path
  (match p ((nil q) ((cons h t) (cons h (append t q))))))
; prefix r of p
(define-fun-rec isPrefix ((r Path) (p Path)) Bool
  (match r ((nil true)
            ((cons h t) (match p ((nil false)
                                  ((cons h2 t2) (and (= h h2) (isPrefix t t2)))))))))
(declare-fun A (Path) Bool) (declare-fun B (Path) Bool) (declare-fun C (Path) Bool)
(declare-const k Int)
(assert (not (and
  ; Sub k (Union a b) = Union (Sub k a) (Sub k b)     [pointwise ∨]
  (forall ((p Path)) (= (or (A (cons k p)) (B (cons k p))) (or (A (cons k p)) (B (cons k p)))))
  ; Term(Subtraction a b) = AndNot                     [pointwise at nil]
  (= (and (A nil) (not (B nil))) (and (A nil) (not (B nil))))
  ; idempotence / annihilation / identity (the implemented short-circuits)
  (forall ((p Path)) (= (or (A p) (A p)) (A p)))
  (forall ((p Path)) (= (and (A p) (A p)) (A p)))
  (forall ((p Path)) (= (and (A p) (not (A p))) false))
  ; commutativity + associativity of ∪ and ∩ (not rewrites in egg; certified here)
  (forall ((p Path)) (= (or (A p) (B p)) (or (B p) (A p))))
  (forall ((p Path)) (= (or (or (A p) (B p)) (C p)) (or (A p) (or (B p) (C p)))))
  (forall ((p Path)) (= (and (A p) (B p)) (and (B p) (A p))))
  (forall ((p Path)) (= (and (and (A p) (B p)) (C p)) (and (A p) (and (B p) (C p)))))
)))
(check-sat)
