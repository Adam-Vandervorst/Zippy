; ISEMPTY / KEYS ON FINITE TRIES.  Tries are the INDUCTIVE ADT below (finite by construction);
; isEmptyT / memT are STRUCTURALLY RECURSIVE, so the movement spec's Keys/IsEmpty mutual recursion
; that this file models TERMINATES by structural descent (height-founded).  The theorem
;   wf(t) ⇒ ( isEmptyT(t) ⟺ ∀p. ¬memT(t,p) )
; requires the trie WELL-FORMEDNESS invariant (no duplicate child keys — the provers correctly
; refuted the unconditional statement: a shadowed non-empty entry falsifies it), and is proved by
; an explicit mutual structural-induction schema plus the shadowing lemma
;   notin(j,l) ⇒ getk(l,j) = the empty node.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-datatypes ((FTrie 0) (FKV 0))
  (((fnode (fterm Bool) (fkids FKV)))
   ((fknil) (fkcons (fkey Int) (fval FTrie) (frest FKV)))))
(declare-fun getk (FKV Int) FTrie)
(assert (forall ((k Int)) (= (getk fknil k) (fnode false fknil))))
(assert (forall ((j Int) (v FTrie) (r FKV) (k Int))
  (= (getk (fkcons j v r) k) (ite (= k j) v (getk r k)))))
(declare-fun memT (FTrie Path) Bool)
(assert (forall ((t FTrie)) (= (memT t nil) (fterm t))))
(assert (forall ((t FTrie) (k Int) (q Path)) (= (memT t (cons k q)) (memT (getk (fkids t) k) q))))
(assert (forall ((p Path)) (not (memT (fnode false fknil) p))))    ; the empty node has no members
(declare-fun isEmptyT (FTrie) Bool)
(declare-fun allEmptyK (FKV) Bool)
(assert (forall ((t FTrie)) (= (isEmptyT t) (and (not (fterm t)) (allEmptyK (fkids t))))))
(assert (= (allEmptyK fknil) true))
(assert (forall ((j Int) (v FTrie) (r FKV))
  (= (allEmptyK (fkcons j v r)) (and (isEmptyT v) (allEmptyK r)))))
; well-formedness: no duplicate keys (recursively)
(declare-fun notin (Int FKV) Bool)
(assert (forall ((j Int)) (notin j fknil)))
(assert (forall ((j Int) (i Int) (v FTrie) (r FKV))
  (= (notin j (fkcons i v r)) (and (not (= j i)) (notin j r)))))
(declare-fun wfK (FKV) Bool)
(declare-fun wfT (FTrie) Bool)
(assert (= (wfK fknil) true))
(assert (forall ((j Int) (v FTrie) (r FKV))
  (= (wfK (fkcons j v r)) (and (notin j r) (wfT v) (wfK r)))))
(assert (forall ((b Bool) (l FKV)) (= (wfT (fnode b l)) (wfK l))))
; shadowing lemma by its own induction schema:  notin(j,l) ⇒ getk(l,j) = empty node
(define-fun PG ((l FKV)) Bool (forall ((j Int)) (=> (notin j l) (= (getk l j) (fnode false fknil)))))
; ASSUMED: T1
(assert (=> (and (PG fknil) (forall ((i Int) (v FTrie) (r FKV)) (=> (PG r) (PG (fkcons i v r)))))
            (forall ((l FKV)) (PG l))))
; main mutual induction
(define-fun PT ((t FTrie)) Bool (=> (wfT t) (= (isEmptyT t) (forall ((p Path)) (not (memT t p))))))
(define-fun PK ((l FKV)) Bool
  (=> (wfK l) (= (allEmptyK l) (forall ((k Int) (p Path)) (not (memT (getk l k) p))))))
; ASSUMED: T1
(assert (=> (and (PK fknil)
                 (forall ((j Int) (v FTrie) (r FKV)) (=> (and (PT v) (PK r)) (PK (fkcons j v r))))
                 (forall ((b Bool) (l FKV)) (=> (PK l) (PT (fnode b l)))))
            (and (forall ((t FTrie)) (PT t)) (forall ((l FKV)) (PK l)))))
(assert (not (forall ((t FTrie)) (PT t))))
(check-sat)
