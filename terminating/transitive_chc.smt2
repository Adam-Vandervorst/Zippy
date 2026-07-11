; ===========================================================================
; FAILED ATTEMPT - kept and annotated because the failure mode is the
; interesting/useful part. See transitive_equiv.smt2 (Z3, ordinary quantified
; SMT) and transitive_equiv.p (Vampire, TPTP FOF) for the proof that actually
; goes through.
;
; The goal was: prove that the doubling recursion
;   R"transitive"(edges) := edges \/ R"transitive"(edges \/ edges.iter(...))
; denotes the same relation as the textbook one-hop transitive closure, for
; EVERY graph, using Z3's Spacer/PDR (Constrained Horn Clause) engine, with
; `edge` left as a fully uninterpreted relation so the result would quantify
; over every possible graph.
;
; Running this file returns "sat" with the witness edge = path = path2 =
; always-false. That looks like "safe" but proves nothing: a sanity check
; (see the sibling file /tmp/sanity_false.smt2 from the session, reproduced
; below in spirit) asserting a DELIBERATELY FALSE claim - "every path2 edge
; is a direct edge", which is obviously false in general since path2
; includes multi-hop connections - ALSO comes back "sat" with the same
; trivial witness. So "sat" here is uninformative regardless of whether the
; property is true or false.
;
; Why: `edge` has no defining clause (it's meant to range over "any graph"),
; so Spacer is free to interpret it - and hence path/path2, which are only
; *lower-bounded* by their defining Horn clauses, not pinned to exactly
; their least fixpoints - as identically false. That trivially satisfies
; every Horn implication here, Spacer reports it as a witness, and the
; result has nothing to do with the actual property. Horn-clause SAT
; without minimality is checking "does some (possibly degenerate)
; interpretation exist", not "does the property hold for the least
; fixpoint, for every input" - the latter is what's actually wanted, and it
; needs the least-fixpoint minimality condition stated as an explicit axiom
; (which is exactly what transitive_equiv.{smt2,p} do).
; ===========================================================================

(set-logic HORN)

(declare-sort Node 0)

(declare-fun edge (Node Node) Bool)
(declare-fun path (Node Node) Bool)
(declare-fun path2 (Node Node) Bool)

; --- path: standard one-hop transitive closure
(assert (forall ((x Node) (y Node))
  (=> (edge x y) (path x y))))
(assert (forall ((x Node) (y Node) (z Node))
  (=> (and (edge x z) (path z y)) (path x y))))

; --- path2: doubling / self-composition, exactly R"transitive"'s recursion
(assert (forall ((x Node) (y Node))
  (=> (edge x y) (path2 x y))))
(assert (forall ((x Node) (y Node) (z Node))
  (=> (and (path2 x z) (path2 z y)) (path2 x y))))

; --- Goal 1: path(x,y) => path2(x,y)  (doubling misses nothing one-hop finds)
(assert (forall ((x Node) (y Node))
  (=> (and (path x y) (not (path2 x y))) false)))

; --- Goal 2: path2(x,y) => path(x,y)  (doubling invents nothing one-hop can't reach)
(assert (forall ((x Node) (y Node))
  (=> (and (path2 x y) (not (path x y))) false)))

(check-sat)
(get-model)
