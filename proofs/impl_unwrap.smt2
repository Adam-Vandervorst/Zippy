; IMPLEMENTATION CHARACTERIZATION (unwrap): memT(unwrap(k,t), p) ⟺ memT(t, k·p).  Direct.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-sort FT 0)
(declare-fun memT (FT Path) Bool)
(declare-fun unw (Int FT) FT)
(assert (forall ((k Int) (t FT) (p Path)) (= (memT (unw k t) p) (memT t (cons k p)))))
(assert (not (forall ((k Int) (t FT) (p Path)) (= (memT (unw k t) p) (memT t (cons k p))))))
(check-sat)
