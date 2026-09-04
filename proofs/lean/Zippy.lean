/-
The package root.  Every module of the Lean development is imported here, so `lake build` (and
therefore `scripts/check_lean.sh`, and therefore `sbt check`) checks all of it and a module that
stops compiling cannot hide by having no importer.

  Syntax     — the MORKL `Space`/`Path` grammar, free variables, size.  ONE syntax for the package.
  Pointwise  — its denotational semantics on the pointwise fragment, and `wrap_roundtrip`.
  Subst      — the one substitution, and its hygiene theorems (plan.md 1E.1).
  PathInduction — T1 discharged: the induction SCHEMA over `path`, and `mon_cancel` (1E.3).
  Fixpoint   — T2 discharged: the four bridging inductions of fixpoint_is_lfp.smt2 (1E.3).
  Counting   — T7 is NOT discharged (it axiomatises an uninterpreted measure); this is a
               MODEL of it, so the residual `PROVED-MODULO T7` is non-vacuous (1E.3).
  Positive   — the positive fragment as a decision procedure, monotonicity and omega-continuity per
               constructor, and the all-k approximant theorem (2E.1).  O10b's Lean half.
  Supercompile — the fold theorem, parametric in `LawOK`: a call-positive residual system's least
               fixpoint is the original meaning under the fix/productivity premises (2E.2).  O12b.
  Whistle    — Kruskal's tree theorem from Mathlib's Higman lemma, and the whistle's termination
               as well-foundedness of whistle-free path extension (2E.3).  O12d / T3.
  Zipper     — the universal zipper refinement theorem over the syntax: `transpileZ`'s cursor
               observes exactly `denT`, every constructor, with the materialisation boundaries
               named (2A.4).  What the stage-2 pipeline cells instantiate.
  WhistleTrace — GENERATED.  The whistle correspondence: every pair `Matching.embeds` compared in
               the seeded drives, re-decided by `embedsB` (2E.3).  See Matching.toLabel.
  Trace      — GENERATED.  The correspondence trace: every substitution the Scala actually
               performed, re-checked against `substS` (1E.2).  See LeanRender.scala.
-/
import Zippy.Syntax
import Zippy.Pointwise
import Zippy.Subst
import Zippy.PathInduction
import Zippy.Fixpoint
import Zippy.Counting
import Zippy.Positive
import Zippy.Supercompile
import Zippy.Whistle
import Zippy.Zipper
import Zippy.Trace
import Zippy.WhistleTrace
