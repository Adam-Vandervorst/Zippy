; The four stepping-stone lemmas of datalog_b_seminaive_terminates.p, re-proved from the BASE
; axioms only (no lemma imports) — one push/pop goal each (the single negated 4-way conjunction
; defeats the case split, each goal alone is instant).
; This makes the whole import chain machine-checked:
;   these lemmas  +  bounded_growth_decrease.smt2  ⊢  datalog_b_seminaive_terminates.smt2.
;
; REGRESSION AND ITS DIAGNOSIS (z3 5.1.0, 2026-08-31).  This file used to report 4/4 unsat and
; started answering
;     unsat / unsat / timeout          (z3 -T:240, i.e. the third goal ate the whole budget and
;                                       the fourth never ran)
; on z3 5.1.0.  The third goal, `stalled_delta_empty`, is TRUE and is not hard:
;     allp(a,dl) = a  =>  setminus(d dl, a) subset= a, and setminus(d dl, a) is DISJOINT from a
;     by construction, so it is empty.
; What changed is not the mathematics but the INSTANTIATION.  The proof needs extensionality at
; (deltap(a,dl), empty) — a pair of terms z3's E-matcher never builds, because the extensionality
; axiom's only patterns lie under its own inner quantifier.  In ONE-SHOT mode z3's macro finder
; inlines `allp`/`deltap` (they are macros: a single universally-quantified defining equation
; each), the goal collapses to the pure `cup`/`setminus` shape, and MBQI closes it in 0.02 s.  In
; INCREMENTAL (push/pop) mode the macro finder is OFF, the definitions stay uninterpreted, and the
; instance is never found.  Measured, on the unmodified file:
;     z3 -T:60  datalog_b_seminaive_lemmas.smt2                      -> unsat unsat timeout
;     z3 -T:60  smt.macro_finder=true datalog_b_seminaive_lemmas.smt2 -> unsat unsat unsat unsat (0.011 s)
;     vampire --input_syntax smtlib2 -t 60s <goal 3 alone>            -> Time limit (60 s, 1.3 GB)
; So NEITHER prover closes it unaided: vampire saturates without finding the refutation either.
;
; THE FIX IS THREE STAGING LEMMAS, not a solver flag and not a weaker statement.  Each is proved
; here as its own push/pop goal from the base axioms and only then asserted, with an explicit
; trigger, so the instantiation z3 cannot guess is NAMED:
;     empty_by_subset_and_disjoint  — a set below `a` and disjoint from `a` is empty
;                                     (this is the extensionality instance, isolated);
;     delta_disjoint_from_all       — the delta is disjoint from `all` (mem-level, immediate);
;     stalled_delta_subset          — a stalled `all` puts the next delta below `all`.
; With those three the original goal closes in 0.01 s, unchanged in statement.  The goal count in
; terminating/run.sh moves 4 -> 7 accordingly; the four ORIGINAL goals are all still here, in
; their original order relative to one another and with their original text.
(declare-sort Node 0)
(declare-sort NSet 0)
(declare-fun mem (Node NSet) Bool)
(declare-fun subset (NSet NSet) Bool)
(declare-fun setminus (NSet NSet) NSet)
(declare-fun cup (NSet NSet) NSet)
(declare-const empty NSet)
(declare-const top NSet)
(declare-fun flag (NSet) Int)
(declare-fun d (NSet) NSet)
(declare-fun allp (NSet NSet) NSet)
(declare-fun deltap (NSet NSet) NSet)
(assert (forall ((x Node) (a NSet) (b NSet))
  (= (mem x (cup a b)) (or (mem x a) (mem x b)))))
(assert (forall ((x Node) (a NSet) (b NSet))
  (= (mem x (setminus a b)) (and (mem x a) (not (mem x b))))))
(assert (forall ((a NSet) (b NSet))
  (= (subset a b) (forall ((x Node)) (=> (mem x a) (mem x b))))))
(assert (forall ((a NSet) (b NSet))
  (=> (forall ((x Node)) (= (mem x a) (mem x b))) (= a b))))
(assert (forall ((x Node)) (not (mem x empty))))
(assert (forall ((x Node)) (mem x top)))
(assert (= (flag empty) 0))
; DEFINITION
(assert (forall ((a NSet)) (=> (distinct a empty) (= (flag a) 1))))
(assert (forall ((a NSet) (dl NSet)) (= (allp a dl) (cup a (setminus (d dl) a)))))
(assert (forall ((a NSet) (dl NSet)) (= (deltap a dl) (setminus (d dl) a))))
; allp_grows
(push)
(assert (not (forall ((a NSet) (dl NSet)) (subset a (allp a dl)))))
(check-sat)
(pop)
; allp_in_top
(push)
(assert (not (forall ((a NSet) (dl NSet)) (subset (allp a dl) top))))
(check-sat)
(pop)
; --- STAGING (see header): the extensionality instance, isolated and named.
; empty_by_subset_and_disjoint: s subset= a and s disjoint from a  =>  s = empty.
(push)
(assert (not (forall ((s NSet) (a NSet))
  (=> (and (subset s a) (forall ((x Node)) (=> (mem x s) (not (mem x a))))) (= s empty)))))
(check-sat)
(pop)
(assert (forall ((s NSet) (a NSet)) (!
  (=> (and (subset s a) (forall ((x Node)) (=> (mem x s) (not (mem x a))))) (= s empty))
  :pattern ((subset s a)))))
; delta_disjoint_from_all: the delta is `d dl` MINUS `a`, so no element of it is in `a`.
(push)
(assert (not (forall ((a NSet) (dl NSet) (x Node)) (=> (mem x (deltap a dl)) (not (mem x a))))))
(check-sat)
(pop)
(assert (forall ((a NSet) (dl NSet) (x Node)) (!
  (=> (mem x (deltap a dl)) (not (mem x a))) :pattern ((mem x (deltap a dl))))))
; stalled_delta_subset: if `all` did not move then the delta it would have added is already in it.
(push)
(assert (not (forall ((a NSet) (dl NSet)) (=> (= (allp a dl) a) (subset (deltap a dl) a)))))
(check-sat)
(pop)
(assert (forall ((a NSet) (dl NSet)) (!
  (=> (= (allp a dl) a) (subset (deltap a dl) a)) :pattern ((allp a dl) (deltap a dl)))))
; stalled_delta_empty: a stalled `all` forces the next delta empty
(push)
(assert (not (forall ((a NSet) (dl NSet)) (=> (= (allp a dl) a) (= (deltap a dl) empty)))))
(check-sat)
(pop)
; flag_bounds
(push)
(assert (not (forall ((a NSet)) (and (>= (flag a) 0) (<= (flag a) 1)))))
(check-sat)
(pop)
