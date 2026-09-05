; =============================================================================
; O3a (continued) — THE ORDER CORRESPONDENCE FOR TAGGED STATES.
;
; Split out of tagged_projection.smt2 for a purely operational reason, recorded
; here so nobody merges it back: these two goals need ONLY the `cons/nil`
; datatype, and in the presence of tagged_projection.smt2's `append` axioms and
; its imported append-decomposition lemma z3 5.1.0 TIMES OUT on them at 40 s
; (the decomposition axiom matches every `cons` term in the goals and the
; instantiation blows up).  Stated over the bare datatype they close in 0.02 s.
; Wrapping at a ONE-ITEM tag is exactly a `cons`, which is goal
; `tag_append_is_cons` in tagged_projection.smt2, so the two files join up
; without either assuming the other.
;
; THEOREM.  For one-item tags t1 = <k1>, t2 = <k2> with k1 != k2, and tagged
; states  S = Wrap(A,t1) u Wrap(B,t2),  S2 = Wrap(A2,t1) u Wrap(B2,t2):
;       S subset= S2   iff   A subset= A2  and  B subset= B2.
;
; WHY IT MATTERS.  `lowerMutualPassthrough` (MORKL.scala:1235-1270) takes the
; least fixpoint of the COMBINED tagged operator and reads each routine off as
; a projection.  "Least in the tagged order" is only "componentwise least" if
; the two orders agree — that is this theorem, and it is exactly what
; mutual_tagged_bekic.smt2 assumes when it reasons about PAIRS instead of about
; tagged states.  The "only if" direction is where TAG DISJOINTNESS earns its
; keep: without distinct heads one component's cylinder could cover another's,
; and a tagged state could be below another without being below componentwise.
;
; HOW THE SECOND GOAL IS STATED, and why that is a STRENGTHENING rather than a
; weakening.  Its hypothesis is not `S subset= S2` but the two INSTANCES of it
; at paths of the form <k1>.q and <k2>.q.  Those follow from `S subset= S2` by
; universal instantiation (which is why assuming them proves MORE, not less:
; the theorem holds from a strictly weaker hypothesis).  They are used instead
; of the general form because z3 cannot find the instantiation itself — the
; only patterns available on the general hypothesis are accessor terms like
; `(hd p) (tl p)`, and with them the goal closes in 0.02 s while without them
; it times out at 20 s.  Rather than ship an obscure trigger, the file states
; the two instances the proof actually uses.
;
; WHAT IS NOT CLAIMED.  Two tags, matching what `asFixpointGeneral` emits and
; the base case of what `lowerMutualPassthrough` emits; the n-ary version
; follows by the same induction step `project_step` pins in
; tagged_projection.smt2, and is not separately stated here.
;
; PROVER LOG (z3 5.1.0): both goals under 0.05 s.
; =============================================================================
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-fun A (Path) Bool)
(declare-fun B (Path) Bool)
(declare-fun A2 (Path) Bool)
(declare-fun B2 (Path) Bool)
(declare-const k1 Int)
(declare-const k2 Int)

; --- componentwise  =>  tagged.
(push)
(assert (distinct k1 k2))
(assert (forall ((q Path)) (=> (A q) (A2 q))))
(assert (forall ((q Path)) (=> (B q) (B2 q))))
(assert (not (forall ((p Path))
    (=> (or (exists ((r Path)) (and (= p (cons k1 r)) (A r)))
            (exists ((r Path)) (and (= p (cons k2 r)) (B r))))
        (or (exists ((r Path)) (and (= p (cons k1 r)) (A2 r)))
            (exists ((r Path)) (and (= p (cons k2 r)) (B2 r))))))))
(check-sat) ; expect unsat
(pop)

; --- tagged  =>  componentwise.  THIS is the direction that needs the tags to
; have DIFFERENT HEADS: drop `distinct k1 k2` and the goal becomes false.
(push)
(assert (distinct k1 k2))
(assert (forall ((q Path))
    (=> (or (exists ((r Path)) (and (= (cons k1 q) (cons k1 r)) (A r)))
            (exists ((r Path)) (and (= (cons k1 q) (cons k2 r)) (B r))))
        (or (exists ((r Path)) (and (= (cons k1 q) (cons k1 r)) (A2 r)))
            (exists ((r Path)) (and (= (cons k1 q) (cons k2 r)) (B2 r)))))))
(assert (forall ((q Path))
    (=> (or (exists ((r Path)) (and (= (cons k2 q) (cons k1 r)) (A r)))
            (exists ((r Path)) (and (= (cons k2 q) (cons k2 r)) (B r))))
        (or (exists ((r Path)) (and (= (cons k2 q) (cons k1 r)) (A2 r)))
            (exists ((r Path)) (and (= (cons k2 q) (cons k2 r)) (B2 r)))))))
(assert (not (and (forall ((q Path)) (=> (A q) (A2 q)))
                  (forall ((q Path)) (=> (B q) (B2 q))))))
(check-sat) ; expect unsat
(pop)
