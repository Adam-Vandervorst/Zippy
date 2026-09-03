; PROVER-BUDGET-EXCEEDED: NEITHER z3 NOR vampire discharged this obligation.  The goal
; below is the real, un-folded structural equivalence (both sides are the actual
; denotations — no constant folding), it is NOT weakened to something provable, and it is
; NOT counted as a discharged cell.  Equivalence for this instance is carried by the
; Scala executor gates (assertEquals against the reference on this input) and by the
; data-agnostic twin; this file records the open obligation and the attempt log.
; ATTEMPT LOG:
; ∀-path goal            z3 timeout    vampire none       (budget 60s each; timings are in the run log, not here — a wall clock in a committed artifact makes it differ from itself on every run)
; 27 observations        z3 timeout    vampire none       (budget 60s each; timings are in the run log, not here — a wall clock in a committed artifact makes it differ from itself on every run)
; ELIDED-GOAL: THE OBLIGATION IS NOT IN THIS FILE.  It is too large to commit, and is recorded
; by identity instead.  IT WAS RENDERED IN FULL AND BOTH PROVERS WERE RUN ON IT — the ATTEMPT
; LOG above is that run.  The goal was NOT weakened, NOT folded, and is NOT counted as
; discharged; this cell is OPEN exactly as the header says.
; rendered size   174134331 bytes
; sha256          7eb9d7c424e400d0823fa6534c71f6933c433776589faaf7046e31c6a59a39e6
; regenerate      ZIPPY_REGENERATE=1 sbt 'testOnly morkl.EquivPipelineTest'
; full text       target/pipeline-elided/puzzle15-space.smt2 (git-ignored; written on every run)
; WHY: 174 MB of rendered denotation is past GitHub's 100 MB per-file limit and past what
; either prover consumed.  See `bodyCapBytes` in EquivPipelineTest for the whole argument.
