; ===========================================================================
; General (unbounded, symbolic-graph) proof that the doubling recursion
;   R"transitive"(edges) := edges \/ R"transitive"(edges \/ edges.iter(...))
; denotes the same relation as the textbook one-hop transitive closure, for
; EVERY graph.
;
; `path`  = one-hop transitive closure: least X with edge(x,y)->X(x,y) and
;           edge(x,z) & X(z,y) -> X(x,y).
; `path2` = doubling/self-composition: least X with edge(x,y)->X(x,y) and
;           X(x,z) & X(z,y) -> X(x,y). This is exactly R"transitive"'s
;           recursion: R"transitive"(E) unrolls to the least X with
;           X = E \/ (X o X).
;
; A naive Horn-clause encoding checked with Z3's CHC/Spacer engine (see
; transitive_chc.smt2 for the attempt) is UNSOUND for this style of
; property: with `edge` left as a completely free/uninterpreted relation
; and no seed facts, the trivial all-false model satisfies every Horn
; clause regardless of whether the intended property is true or false (a
; sanity check with a deliberately FALSE claim also came back "sat",
; confirming the encoding proves nothing). That happens because "path is
; the least relation satisfying its clauses" is a second-order minimality
; condition that plain Horn-SAT (or Spacer's reachability search over a
; relation with zero seed facts) does not capture.
;
; The fix: state that minimality condition as an explicit first-order
; axiom schema and INSTANTIATE it at exactly the predicates the proof
; needs (path2, and a "transitivity witness" predicate for path itself).
; Once minimality is an axiom instead of an implicit assumption, this
; becomes ordinary quantified SMT validity checking, which Z3 handles
; natively (no CHC engine needed).
; ===========================================================================

(declare-sort Node 0)
(declare-fun edge (Node Node) Bool)
(declare-fun path (Node Node) Bool)
(declare-fun path2 (Node Node) Bool)

; --- defining (inductive-step) axioms: path/path2 each CONTAIN at least
; these facts (this direction alone is just Horn implication, no minimality
; needed yet).
(assert (forall ((x Node) (y Node))
  (=> (edge x y) (path x y))))
(assert (forall ((x Node) (y Node) (z Node))
  (=> (and (edge x z) (path z y)) (path x y))))

(assert (forall ((x Node) (y Node))
  (=> (edge x y) (path2 x y))))
(assert (forall ((x Node) (y Node) (z Node))
  (=> (and (path2 x z) (path2 z y)) (path2 x y))))

; --- path's minimality, instantiated at Q := path2. path is DEFINED as the
; LEAST relation closed under [edge x y -> Q x y] and [edge x z & Q z y ->
; Q x y]; this schema instance says: if path2 also satisfies those two
; closure conditions, path must be contained in path2.
(assert (=>
  (and
    (forall ((x Node) (y Node)) (=> (edge x y) (path2 x y)))
    (forall ((x Node) (y Node) (z Node)) (=> (and (edge x z) (path2 z y)) (path2 x y))))
  (forall ((x Node) (y Node)) (=> (path x y) (path2 x y)))))

; --- path's minimality again, instantiated at Q(x,y) := (forall c. path(y,c)
; -> path(x,c)) - "everything reachable from y is reachable from x". This
; specific instantiation is exactly what's needed to derive path's own
; transitivity from its two defining axioms (an inductive fact, not one of
; the axioms directly): closure under edge follows straight from path's
; second defining axiom (both base and step cases below), so path's
; minimality then hands us transitivity as its conclusion.
(assert (=>
  (and
    (forall ((x Node) (y Node))
      (=> (edge x y) (forall ((c Node)) (=> (path y c) (path x c)))))
    (forall ((x Node) (y Node) (w Node))
      (=> (and (edge x w) (forall ((c Node)) (=> (path y c) (path w c))))
          (forall ((c Node)) (=> (path y c) (path x c))))))
  (forall ((x Node) (y Node)) (=> (path x y) (forall ((c Node)) (=> (path y c) (path x c))))))
  )

; --- path2's minimality, instantiated at Q := path. Symmetric to the first
; instantiation above: path2 is the least relation closed under [edge x y ->
; Q x y] and [Q x z & Q z y -> Q x y] (self-composition, not edge-composition);
; path satisfies both once we have path's own transitivity in hand.
(assert (=>
  (and
    (forall ((x Node) (y Node)) (=> (edge x y) (path x y)))
    (forall ((x Node) (y Node) (z Node)) (=> (and (path x z) (path z y)) (path x y))))
  (forall ((x Node) (y Node)) (=> (path2 x y) (path x y)))))

; --- negate the goal: path and path2 disagree on some concrete pair
(declare-const x0 Node)
(declare-const y0 Node)
(assert (not (= (path x0 y0) (path2 x0 y0))))

(check-sat)
