; IMPLEMENTATION CHARACTERIZATION (wrap): the trie wrap (one prefix item) has the denotation
;   memT(wrap(k, t), p) ⟺ ∃q. p = k·q ∧ memT(t, q)      — by path case analysis, no induction.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-sort FT 0)
(declare-fun memT (FT Path) Bool)
(declare-fun emp () FT)
(assert (forall ((p Path)) (not (memT emp p))))
(declare-fun wrap (Int FT) FT)
(assert (forall ((k Int) (t FT)) (not (memT (wrap k t) nil))))
(assert (forall ((k Int) (t FT) (j Int) (q Path))
  (= (memT (wrap k t) (cons j q)) (and (= j k) (memT t q)))))
(assert (not (forall ((k Int) (t FT) (p Path))
  (= (memT (wrap k t) p) (exists ((q Path)) (and (= p (cons k q)) (memT t q)))))))
(check-sat)
