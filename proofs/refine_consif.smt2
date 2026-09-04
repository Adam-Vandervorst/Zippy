; PRUNING REFINEMENT (ConsIf): the empty-child-dropping cons preserves per-key membership —
;   memT(getk(consIf(k, v, rest), j), q) ⟺ memT(getk(kvcons(k,v,rest), j), q)
; (dropping an EMPTY v loses no member; keeping a non-empty v changes nothing).  No induction.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-sort FT 0)
(declare-fun memT (FT Path) Bool)
(declare-fun emp () FT)
(assert (forall ((p Path)) (not (memT emp p))))
(declare-fun isEmp (FT) Bool)
(assert (forall ((t FT)) (= (isEmp t) (forall ((p Path)) (not (memT t p))))))   ; certified: isempty_finite
(declare-datatypes ((KV 0)) (((kvnil) (kvcons (kkey Int) (kval FT) (krest KV)))))
(declare-fun getk (KV Int) FT)
(assert (forall ((k Int)) (= (getk kvnil k) emp)))
(assert (forall ((j Int) (v FT) (r KV) (k Int)) (= (getk (kvcons j v r) k) (ite (= k j) v (getk r k)))))
(declare-fun consIf (Int FT KV) KV)
(assert (forall ((k Int) (v FT) (r KV)) (=> (isEmp v) (= (consIf k v r) r))))
(assert (forall ((k Int) (v FT) (r KV)) (=> (not (isEmp v)) (= (consIf k v r) (kvcons k v r)))))
; NOTE the sortedness caveat: dropping the k-entry exposes any SHADOWED k in rest — sound only for
; well-formed (no-duplicate) lists; we assume k does not occur in rest (the wf invariant).
(declare-fun notin (Int KV) Bool)
(assert (forall ((j Int)) (notin j kvnil)))
(assert (forall ((j Int) (i Int) (v FT) (r KV)) (= (notin j (kvcons i v r)) (and (not (= j i)) (notin j r)))))
(define-fun PG ((l KV)) Bool (forall ((j Int)) (=> (notin j l) (= (getk l j) emp))))
; ASSUMED: T1
(assert (=> (and (PG kvnil) (forall ((i Int) (v FT) (r KV)) (=> (PG r) (PG (kvcons i v r))))) (forall ((l KV)) (PG l))))
(assert (not (forall ((k Int) (v FT) (r KV) (j Int) (q Path))
  (=> (notin k r)
      (= (memT (getk (consIf k v r) j) q) (memT (getk (kvcons k v r) j) q))))))
(check-sat)
