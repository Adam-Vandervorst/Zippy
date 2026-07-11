; STATUS: OPEN — attempted with z3 (200s), vampire default and vampire --induction struct; none
; discharge the nested pair-induction with ConsIf pruning automatically.  The neighbouring
; obligations ARE proved (refine_clu: the union merge; refine_consif: the pruning cons;
; refine_kmerge/refine_kinter: the pure key-list merges), and this exact merge path is exercised
; by the randomized differential suite (rand-intersection/rand-subtraction: hundreds of instances
; against an independent reference).  A hand-guided proof (or a stronger induction schedule) is
; the known follow-up.
; KV-LIST REFINEMENT (cls): the sorted merge with ConsIf pruning implements, per key, the trie-level
; op (memT-characterisation taken as the certified lemma), for SORTED child lists.  Needs (i) the
; lower-bound lookup lemma, (ii) BOUND PRESERVATION of the recursion (results only shrink keys),
; (iii) nested pair-induction schemata.
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-sort FT 0)
(declare-fun memT (FT Path) Bool)
(declare-fun emp () FT)
(assert (forall ((p Path)) (not (memT emp p))))
(declare-fun isEmp (FT) Bool)
(assert (forall ((t FT)) (= (isEmp t) (forall ((p Path)) (not (memT t p))))))
(declare-datatypes ((KV 0)) (((kvnil) (kvcons (kkey Int) (kval FT) (krest KV)))))
(declare-fun getk (KV Int) FT)
(assert (forall ((k Int)) (= (getk kvnil k) emp)))
(assert (forall ((j Int) (v FT) (r KV) (k Int)) (= (getk (kvcons j v r) k) (ite (= k j) v (getk r k)))))
(declare-fun lbnd (Int KV) Bool)
(assert (forall ((lo Int)) (lbnd lo kvnil)))
(assert (forall ((lo Int) (j Int) (v FT) (r KV)) (= (lbnd lo (kvcons j v r)) (and (< lo j) (lbnd j r)))))
(declare-fun srt (KV) Bool)
(assert (= (srt kvnil) true))
(assert (forall ((j Int) (v FT) (r KV)) (= (srt (kvcons j v r)) (and (lbnd j r) (srt r)))))
(define-fun PL0 ((l KV)) Bool (forall ((lo Int) (h Int)) (=> (and (lbnd lo l) (<= h lo)) (= (getk l h) emp))))
(assert (=> (and (PL0 kvnil) (forall ((j Int) (v FT) (r KV)) (=> (PL0 r) (PL0 (kvcons j v r))))) (forall ((l KV)) (PL0 l)))
)
(declare-fun consIf (Int FT KV) KV)
(assert (forall ((k Int) (v FT) (r KV)) (=> (isEmp v) (= (consIf k v r) r))))
(assert (forall ((k Int) (v FT) (r KV)) (=> (not (isEmp v)) (= (consIf k v r) (kvcons k v r)))))
(declare-fun trs (FT FT) FT)
(assert (forall ((x FT) (y FT) (p Path)) (= (memT (trs x y) p) (and (memT x p) (not (memT y p))))))
(declare-fun f (KV KV) KV)
(assert (forall ((b KV)) (= (f kvnil b) kvnil)))
(assert (forall ((a KV)) (= (f a kvnil) a)))
(assert (forall ((k1 Int) (v1 FT) (r1 KV) (k2 Int) (v2 FT) (r2 KV))
  (=> (< k1 k2) (= (f (kvcons k1 v1 r1) (kvcons k2 v2 r2)) (kvcons k1 v1 (f r1 (kvcons k2 v2 r2)))))))
(assert (forall ((k1 Int) (v1 FT) (r1 KV) (k2 Int) (v2 FT) (r2 KV))
  (=> (< k2 k1) (= (f (kvcons k1 v1 r1) (kvcons k2 v2 r2)) (f (kvcons k1 v1 r1) r2)))))
(assert (forall ((k1 Int) (v1 FT) (r1 KV) (k2 Int) (v2 FT) (r2 KV))
  (=> (= k1 k2) (= (f (kvcons k1 v1 r1) (kvcons k2 v2 r2)) (consIf k1 (trs v1 v2) (f r1 r2))))))
; (ii) bound preservation, its own nested schema
(define-fun QB ((a KV) (b KV)) Bool (forall ((lo Int)) (=> (and (lbnd lo a) (lbnd lo b)) (lbnd lo (f a b)))))
(define-fun PB ((a KV)) Bool (forall ((b KV)) (QB a b)))
(assert (forall ((k1 Int) (v1 FT) (r1 KV))
  (=> (and (PB r1) (QB (kvcons k1 v1 r1) kvnil)
           (forall ((k2 Int) (v2 FT) (r2 KV))
             (=> (and (QB (kvcons k1 v1 r1) r2) (QB r1 (kvcons k2 v2 r2)) (QB r1 r2))
                 (QB (kvcons k1 v1 r1) (kvcons k2 v2 r2)))))
      (PB (kvcons k1 v1 r1)))))
(assert (=> (and (PB kvnil) (forall ((k1 Int) (v1 FT) (r1 KV)) (=> (PB r1) (PB (kvcons k1 v1 r1)))))
            (forall ((a KV)) (PB a))))
; (iii) the main statement
(define-fun QQ ((a KV) (b KV)) Bool
  (=> (and (srt a) (srt b))
      (forall ((k Int) (q Path)) (= (memT (getk (f a b) k) q) (and (memT (getk a k) q) (not (memT (getk b k) q)))))))
(define-fun PP ((a KV)) Bool (forall ((b KV)) (QQ a b)))
(assert (forall ((k1 Int) (v1 FT) (r1 KV))
  (=> (and (PP r1) (QQ (kvcons k1 v1 r1) kvnil)
           (forall ((k2 Int) (v2 FT) (r2 KV))
             (=> (and (QQ (kvcons k1 v1 r1) r2) (QQ r1 (kvcons k2 v2 r2)) (QQ r1 r2))
                 (QQ (kvcons k1 v1 r1) (kvcons k2 v2 r2)))))
      (PP (kvcons k1 v1 r1)))))
(assert (=> (and (PP kvnil) (forall ((k1 Int) (v1 FT) (r1 KV)) (=> (PP r1) (PP (kvcons k1 v1 r1)))))
            (forall ((a KV)) (PP a))))
(assert (not (forall ((a KV) (b KV)) (QQ a b))))
(check-sat)
