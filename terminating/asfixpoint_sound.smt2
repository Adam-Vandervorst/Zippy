; =============================================================================
; O2 — `asFixpoint` IS SOUND: the Call recursion and the Fixpoint loop compute
; the same value, and stop at the same round.
;
; THE TRANSLATION (MORKL.scala:1214-1222).  A routine of the datalog shape
;
;   r(refs; m_1..m_n) = Mention(m_c) \/ Call r(refs; m_1,..,T,..,m_n)
;
; — every ref and every mention passed through unchanged except ONE, whose new
; value is T, and whose CURRENT value is the union's left arm — is rewritten to
;
;   r(refs; m_1..m_n) = Fixpoint(Mention(m_c), m_c, T).
;
; The two sides are executed by COMPLETELY DIFFERENT interpreter rules, and
; that is what makes this a real obligation rather than a renaming:
;
;   THE CALL RULE (eval, MORKL.scala:284-297) is a recursion with a
;   STABILISED-ARGUMENT CUT.  Writing Ev(X) for the value of the call whose
;   changing argument is X, and T for the argument map,
;       Ev(X) = X                     if T(X) = X          <- the cut fires
;       Ev(X) = X u Ev(T(X))          otherwise
;   (the cut is the `if (mentions zip mentionvs).forall(...)` test: when every
;   argument is a fixed point of its argument map, only the union's LEFT arm is
;   evaluated, which for this shape is exactly `Mention(m_c)`, i.e. X.)
;
;   THE FIXPOINT RULE (exec/execT, MORKL.scala:652-670) is a FORWARD LOOP with
;   an accumulator: C_0 = X, C_{k+1} = T(C_k), A_0 = C_0, A_{k+1} = A_k u C_{k+1},
;   returning A_n at the least n with C_{n+1} = C_n.
;
; One recurses DOWNWARD from the initial argument and unions on the way back
; out; the other iterates UPWARD and unions on the way in.  They agree, and
; this file proves it.
;
; THEOREM.  Let n be an index with C_{n+1} = C_n (the loop's stopping test) and
; let Ev be the call-side value defined on 0..n by
;       Ev(n) = C_n,        Ev(j) = C_j u Ev(j+1)  for 0 <= j < n.
; Then
;   (VALUE)  Ev(0) = A_n     — the call returns exactly what the loop returns;
;   (STOP)   the two stopping tests are the SAME predicate `T(C_n) = C_n`, so
;            neither side can stop where the other would not: the cut fires at
;            round j iff C_{j+1} = C_j, which is the loop's test verbatim.
; (STOP) is not a separate proof obligation once the recurrences are written
; down as above — it is visible in the two definitions, and it is called out
; because it is the half a reader is most likely to assume rather than check:
; if the cut fired on a WEAKER condition (say, "the output stopped growing")
; the two sides would differ, and `asFixpoint` would be unsound.  Goal
; `cut_test_is_loop_test` below pins it: at a stationary index the call-side
; value is already its own limit.
;
; WHAT IS NOT CLAIMED.  Nothing about T (it is uninterpreted, as `frontier` is
; in reachable_decrease.p), nothing about whether n EXISTS (that is O1(iv) +
; no_infinite_descent.smt2), and nothing about the SYNTACTIC side conditions
; `asFixpoint` checks — that every other argument is passed through unchanged
; and that the union's left arm is exactly `Mention(m_c)`.  Those are a pattern
; match on the AST (MORKL.scala:1216-1220), they are what makes T well defined
; as a function of the changing mention alone, and they are assumed here.  Note
; in particular that this shape is INFLATIONARY-FREE: the theorem below does
; NOT need T monotone, because both sides accumulate the union of the SAME
; chain.  That is exactly why `asFixpoint`, unlike `asFixpointGeneral` and
; `lowerMutualPassthrough`, needs no monotonicity gate.
;
; PROVER LOG (z3 5.1.0).  Same staging discipline as fixpoint_is_lfp.smt2:
; antisymmetry and the union laws are proved and asserted with demand-driven
; triggers before the Int-indexed chains exist.  The one genuinely awkward step
; is the DOWNWARD induction for `Ev(0) subset= A_n`, which is run as an upward
; induction on the gap d = n - j.
; =============================================================================
(declare-sort Node 0)
(declare-sort NSet 0)
(declare-fun mem (Node NSet) Bool)
(declare-fun subset (NSet NSet) Bool)
(declare-fun cup (NSet NSet) NSet)
(assert (forall ((x Node) (a NSet) (b NSet)) (= (mem x (cup a b)) (or (mem x a) (mem x b)))))
(assert (forall ((a NSet) (b NSet)) (= (subset a b) (forall ((x Node)) (=> (mem x a) (mem x b))))))
(assert (forall ((a NSet) (b NSet)) (=> (forall ((x Node)) (= (mem x a) (mem x b))) (= a b))))

; --- stepping stones (proved, then asserted with demand-driven triggers).
(push)
(assert (not (forall ((a NSet) (b NSet)) (=> (and (subset a b) (subset b a)) (= a b)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet)) (!
  (=> (and (subset a b) (subset b a)) (= a b)) :pattern ((subset a b) (subset b a)))))
(push)
(assert (not (forall ((a NSet)) (subset a a))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet)) (! (subset a a) :pattern ((subset a a)))))
(push)
(assert (not (forall ((a NSet) (b NSet) (c NSet)) (=> (and (subset a b) (subset b c)) (subset a c)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet) (c NSet)) (!
  (=> (and (subset a b) (subset b c)) (subset a c)) :pattern ((subset a b) (subset b c)))))
(push)
(assert (not (forall ((a NSet) (b NSet)) (and (subset a (cup a b)) (subset b (cup a b))))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet)) (!
  (and (subset a (cup a b)) (subset b (cup a b))) :pattern ((cup a b)))))
(push)
(assert (not (forall ((a NSet) (b NSet) (c NSet))
  (=> (and (subset a c) (subset b c)) (subset (cup a b) c)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet) (c NSet)) (!
  (=> (and (subset a c) (subset b c)) (subset (cup a b) c)) :pattern ((cup a b) (subset a c)))))

; =============================================================================
; THE TWO EXECUTIONS.  T is UNINTERPRETED.  `n` is a stationary index of the
; chain; it is a constant, not assumed least, and nothing below needs it least.
; =============================================================================
(declare-fun T (NSet) NSet)
(declare-const arg NSet)                                       ; the initial argument
(declare-const n Int)
(assert (>= n 0))

(declare-fun C (Int) NSet)                                     ; C_k = T^k(arg)
(assert (= (C 0) arg))
(assert (forall ((k Int)) (! (=> (>= k 0) (= (C (+ k 1)) (T (C k)))) :pattern ((C (+ k 1))))))
(assert (= (C (+ n 1)) (C n)))                                 ; the loop's stopping test

(declare-fun A (Int) NSet)                                     ; the Fixpoint loop's accumulator
(assert (= (A 0) (C 0)))
(assert (forall ((k Int)) (! (=> (>= k 0) (= (A (+ k 1)) (cup (A k) (C (+ k 1))))) :pattern ((A (+ k 1))))))

(declare-fun Ev (Int) NSet)                                    ; the Call rule's returned value
(assert (= (Ev n) (C n)))
(assert (forall ((j Int)) (!
  (=> (and (>= j 0) (< j n)) (= (Ev j) (cup (C j) (Ev (+ j 1))))) :pattern ((Ev j)))))

; =============================================================================
; (a) A is ASCENDING and dominates every iterate up to n:  C_k subset= A_k
; subset= A_n for 0 <= k <= n.  (Upward induction on k, then on the gap.)
; =============================================================================
(push)
(assert (not (forall ((k Int)) (=> (>= k 0) (and (subset (A k) (A (+ k 1))) (subset (C k) (A k)))))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((k Int)) (!
  (=> (>= k 0) (and (subset (A k) (A (+ k 1))) (subset (C k) (A k)))) :pattern ((A k)))))
; --- A_k subset= A_n for k <= n, by induction on the gap d = n - k.
(push)
(assert (not (subset (A n) (A n))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const d0 Int)
(assert (and (>= d0 0) (<= d0 n)))
(assert (subset (A (- n d0)) (A n)))
(assert (not (=> (<= (+ d0 1) n) (subset (A (- n (+ d0 1))) (A n)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((k Int)) (! (=> (and (>= k 0) (<= k n)) (subset (A k) (A n))) :pattern ((A k)))))

; =============================================================================
; (b) Ev(0) subset= A_n — the DOWNWARD direction, run as an induction on the
; gap d = n - j: every Ev(j) is below A_n.
; =============================================================================
(push)
(assert (not (subset (Ev n) (A n))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const d1 Int)
(assert (and (>= d1 0) (<= d1 n)))
(assert (subset (Ev (- n d1)) (A n)))
(assert (not (=> (<= (+ d1 1) n) (subset (Ev (- n (+ d1 1))) (A n)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((j Int)) (! (=> (and (>= j 0) (<= j n)) (subset (Ev j) (A n))) :pattern ((Ev j)))))

; =============================================================================
; (c) A_n subset= Ev(0) — the UPWARD direction.  Ev is descending in its index
; (Ev(j) = C_j u Ev(j+1)), so every C_k with k <= n is inside Ev(0), and A_n is
; the union of exactly those.
; =============================================================================
(push)
(assert (not (forall ((j Int)) (=> (and (>= j 0) (< j n)) (and (subset (Ev (+ j 1)) (Ev j)) (subset (C j) (Ev j)))))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((j Int)) (!
  (=> (and (>= j 0) (< j n)) (and (subset (Ev (+ j 1)) (Ev j)) (subset (C j) (Ev j))))
  :pattern ((Ev j)))))
; --- Ev(j) subset= Ev(0) for j <= n, by upward induction on j.
(push)
(assert (not (subset (Ev 0) (Ev 0))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const j0 Int)
(assert (and (>= j0 0) (< j0 n)))
(assert (subset (Ev j0) (Ev 0)))
(assert (not (subset (Ev (+ j0 1)) (Ev 0))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((j Int)) (! (=> (and (>= j 0) (<= j n)) (subset (Ev j) (Ev 0))) :pattern ((Ev j)))))
; --- hence every iterate is in Ev(0)...
(push)
(declare-const j1 Int)
(assert (and (>= j1 0) (<= j1 n)))
(assert (not (subset (C j1) (Ev 0))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((j Int)) (! (=> (and (>= j 0) (<= j n)) (subset (C j) (Ev 0))) :pattern ((C j)))))
; --- ...and A_k subset= Ev(0) for k <= n, by upward induction on k.
(push)
(assert (not (subset (A 0) (Ev 0))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const k1 Int)
(assert (and (>= k1 0) (< k1 n)))
(assert (subset (A k1) (Ev 0)))
(assert (not (subset (A (+ k1 1)) (Ev 0))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((k Int)) (! (=> (and (>= k 0) (<= k n)) (subset (A k) (Ev 0))) :pattern ((A k)))))

; =============================================================================
; VALUE: the two sides are equal.  This is the sentence `asFixpoint` needs.
; =============================================================================
(push)
(assert (not (= (Ev 0) (A n))))
(check-sat) ; expect unsat
(pop)

; =============================================================================
; STOP: the cut test IS the loop test.  At the stationary index the call-side
; value has already reached its limit - `Ev(n) = C_n` - so the cut fires exactly
; where the loop halts, and one more round would add nothing on either side.
; =============================================================================
(push)
(assert (not (and (= (Ev n) (C n)) (= (T (C n)) (C n)) (= (A (+ n 1)) (A n)))))
(check-sat) ; expect unsat
(pop)
