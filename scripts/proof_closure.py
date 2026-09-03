#!/usr/bin/env python3
"""THE FULL DEPENDENCY CLOSURE OF EVERY REPORTED PROOF STATUS.

WHY THIS EXISTS.  `PROVED` in a status table is a claim about a machine run, and the run happened
under whatever axioms the file included.  Some of those axioms are DERIVED (a lemma file whose own
obligations are discharged in the same corpus); some are TRUSTED (`docs/TRUSTED.md` enumerates
them, and T1 is an induction SCHEMA that first-order logic cannot even state, so it is asserted).
A reader of the table cannot tell the two apart, because the table reports the verdict of the
prover and the prover does not distinguish an assumption from a theorem.

So an unqualified `PROVED` is only honest when the theorem's TRANSITIVE include closure contains no
trusted assumption.  This script computes that closure from the `include(...)` directives -- the
files themselves, not a hand-maintained dependency column that could drift -- intersects it with the
declared trusted base, and reports every status as either

    PROVED                    -- closure is free of trusted assumptions
    PROVED-MODULO T1[, T2...] -- closure reaches those entries of docs/TRUSTED.md

`--check` makes a status table that claims unqualified `PROVED` for a conditional result an ERROR,
which is the enforcement the review asks for: "a result depending on an admitted schema ... must be
reported as conditional".

WHAT IT DOES NOT DO.  It cannot see a dependency that is not an `include` -- an
implementation-correspondence lemma carried by a test rather than by an axiom file is invisible
here, and `docs/TRUSTED.md` T4/T6 are exactly that kind.  Those are reported as a SEPARATE,
file-level annotation from the trusted base itself, so the output distinguishes "reached through the
axioms" from "declared for this corpus as a whole".
"""

import argparse, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
INCLUDE = re.compile(r"include\('([^']+)'\)")

# ==================================================================================================
# THE EDGE AN `include` GRAPH CANNOT SEE, and the one that made this script miss two conditionals.
#
# An axiom file may RE-ASSERT a lemma that is DISCHARGED ELSEWHERE IN THE SAME CORPUS, as a cheap
# clause, because carrying the real proof's axioms through every consumer's search is too expensive.
# `proofs/unbounded/_cancel.p` is the case: it asserts left-cancellation in one clause, its header
# records that `mon_cancel.p` proves it, and it has NO includes at all -- so the include closure of
# `wrap_roundtrip.p` and `card_wrap.p` reaches `_cancel.p` and stops, never reaching
# `_path_induction.p`.  Both were therefore reported as unqualified `PROVED` while depending on a
# trusted schema, which is exactly what this script exists to prevent, and `docs/TRUSTED.md` T1
# already said so in prose ("Used by: mon_cancel.p, hence _cancel.p, hence wrap_roundtrip.p and
# card_wrap.p").
#
# So the link is read FROM THE FILE, as a `% DISCHARGED-BY: <theorem>.p` marker, rather than from a
# table here: one source of truth, in the file whose status depends on it, and it cannot drift from
# the header prose beside it.  `--check` then verifies that the named theorem exists, is reported,
# and is PROVED -- because an axiom file re-asserting something UNPROVED is a much worse defect than
# the one this edge was added to catch.
# ==================================================================================================
DISCHARGED_BY = re.compile(r"^%\s*DISCHARGED-BY:\s*(\S+)", re.M)

# ==================================================================================================
# EVERY REPORTED STATUS, NOT ONE CORPUS OF FOUR.
#
# The requirement is "enumerate the full dependency closure of EVERY reported theorem status", and
# there are four tables: 178 rows in proofs/STATUS.tsv (the law corpus), 20 in
# terminating/STATUS.tsv, 42 in proofs/pipeline/STATUS.tsv and 78 in proofs/unbounded/STATUS.tsv --
# 318 reported statuses in total.  An earlier revision of this script read only the last of those
# and said nothing about the other 240, which is not an enumeration of every status; it is an
# enumeration of the ones the technique happened to fit.
#
# THE TECHNIQUE ONLY FITS ONE OF THEM, AND THAT IS THE POINT OF SAYING SO.  `include`-closure works
# on the TPTP tier because dependency there IS inclusion.  The three SMT tables have essentially no
# includes (two files across all of proofs/laws, terminating and proofs/pipeline): an SMT obligation
# carries its axioms inline, so what a closure would have to follow is `assert`ions, and deciding
# which of those is a trusted principle rather than a definition is not a graph walk.  So those
# tables are enumerated and classified by the DECLARED, file-scoped trusted entries that apply to
# them, and this script REPORTS them without rewriting their verdicts -- their harnesses own those
# files, and an annotation from here would fight the next run.
# ==================================================================================================
# SIX TABLES, NOT FOUR.  An earlier revision of this list had four and reported "318 reported
# statuses across 4 tables" as if that were all of them; `find . -name STATUS.tsv` returns six.
STATUS_TABLES = [
    (ROOT / "proofs/unbounded/STATUS.tsv",             "unbounded",   "tptp"),
    (ROOT / "proofs/STATUS.tsv",                       "laws",        "smt"),
    (ROOT / "terminating/STATUS.tsv",                  "terminating", "smt"),
    (ROOT / "proofs/pipeline/STATUS.tsv",              "pipeline",    "smt"),
    (ROOT / "proofs/pipeline/fixpoint-gate/STATUS.tsv", "pipeline",   "smt"),
    (ROOT / "proofs/spatial-semantic/STATUS.tsv",      "spatial",     "smt"),
]

# ---------------------------------------------------------------------------------------------
# THE DECLARED TRUSTED BASE.  Keyed by the entry id in docs/TRUSTED.md; `axiom` names the file
# whose inclusion IS the assumption, and `corpus` marks an entry that is not reachable through any
# include and applies to a whole tier instead.
# ---------------------------------------------------------------------------------------------
TRUSTED = {
    "T1": dict(axiom="_path_induction.p", what="structural induction over `path`, at one predicate"),
    # `rows` names the status rows an entry makes conditional DIRECTLY, where the trusted principle
    # is asserted inside a specific obligation file rather than reached through a dependency.  T2's
    # four induction principles are `assert`ed in fixpoint_is_lfp.smt2 itself, so that row is
    # conditional on T2 by inspection and not by any closure.
    "T2": dict(axiom=None, corpus="terminating", rows={"fixpoint_is_lfp"},
               what="the four bridging induction principles of fixpoint_is_lfp.smt2"),
    "T3": dict(axiom=None, corpus="terminating",
               what="the whistle terminates (Kruskal's tree theorem) -- ADMITTED"),
    "T4": dict(axiom=None, corpus="pipeline", what="EquivPipeline.expand, the stage-0 expansion"),
    "T5": dict(axiom=None, corpus="unbounded",
               what="Range is outside the certified pointwise algebra"),
    "T6": dict(axiom=None, corpus="unbounded", what="grounded functions are deterministic"),
    "T7": dict(axiom="_card.p", what="the counting axioms (4 counting + injective-image + pfxmap)"),
}

# THE MARKER THAT MAKES docs/TRUSTED.md's COMPLETENESS CLAIM CHECKABLE.  An axiom file that declares
# an `% ASSUMED` block is asserting something the corpus does not derive, and that is exactly what a
# T entry is for -- so it must name one.  The check exists because the claim was already false:
# `_card.p` declared six assumed counting axioms in its own header and none was a T entry, and
# `card_wrap` was reported as unqualified PROVED on top of them.
ASSUMED_BLOCK = re.compile(r"^%\s*ASSUMED\b", re.M)
TRUSTED_ENTRY = re.compile(r"^%\s*TRUSTED-ENTRY:\s*(T\d+)", re.M)

# ==================================================================================================
# THE MARKER THAT DISCHARGES A TRUSTED ENTRY, RATHER THAN DECLARING ONE (plan.md 0.5).
#
# `TRUSTED-ENTRY` above says "this file asserts something the corpus does not derive".  Its converse
# is `% MECHANIZED-IN: <lean file>#<fully qualified theorem>`: "the principle this file's closure
# reaches is a THEOREM, checked by Lean's kernel, over there".  That is what items 3 and 8 are for --
# T1 is structural induction over `path`, which first-order logic cannot state and a dependently
# typed system gives for free from the inductive declaration -- and it is the only honest way a row
# reported `PROVED-MODULO T1` ever becomes an unqualified `PROVED`.
#
# THE LIFT IS NOT TAKEN ON THE MARKER'S WORD.  A marker is a claim about a file in `proofs/lean`, and
# a claim in a comment is exactly what this script exists to stop being believed.  So a lift requires
# a WITNESS: `scripts/check_lean.sh` builds the package, refuses any `sorry`, resolves every marker,
# runs `#print axioms` on each named theorem, and writes `target/lean-mechanized.tsv`.  This script
# reads that table.  It is under `target/` and NOT committed on purpose: it records what the LOCAL
# toolchain checked, so a reader who has not run the gate gets NO lift rather than inheriting someone
# else's build, and the failure direction is always the conservative one.
# ==================================================================================================
# THE SAME MARKER GRAMMAR AS `scripts/check_lean.sh`, character for character.  The two readers
# must agree on what a marker IS: a marker this script honoured and that one did not witness
# would lift nothing (harmless), but the reverse -- witnessed there, invisible here -- would
# leave a discharged entry reported as still conditional and nobody would know why.  Anchored
# at line start, and `<`, `>`, backtick and `|` are excluded because prose ABOUT the marker is
# made of them: `docs/TRUSTED.md`'s specification table contains the literal placeholder
# `<file>#<thm>` inside a markdown row, and a scan without those exclusions failed the Lean
# gate on a marker nobody had written.
MECHANIZED_IN = re.compile(r"^\s*[%;]\s*MECHANIZED-IN:\s*([^\s`<>|]+)#([^\s`<>|]+)", re.M)
LEAN_WITNESS = ROOT / "target" / "lean-mechanized.tsv"


_witness_cache = {}


def read_lean_witness():
    """{marker -> (theorem, axioms)} for every marker `scripts/check_lean.sh` resolved locally.

    An absent witness is an EMPTY mapping, not an error: the Lean gate has simply not been run here,
    and every marked row stays reported as conditional."""
    if "v" in _witness_cache:
        return _witness_cache["v"]
    out = {}
    _witness_cache["v"] = out
    if not LEAN_WITNESS.is_file():
        return out
    for line in LEAN_WITNESS.read_text().splitlines():
        parts = line.split("\t")
        if len(parts) >= 4 and parts[3].strip() == "MECHANIZED":
            out[parts[0].strip()] = (parts[1].strip(), parts[2].strip())
    return out


def read_trusted_ids():
    """cross-check the table above against docs/TRUSTED.md, so the two cannot drift apart"""
    md = (ROOT / "docs/TRUSTED.md").read_text()
    found = set(re.findall(r"^## (T\d+)\.", md, re.M))
    declared = set(TRUSTED)
    if found != declared:
        print(f"ERROR: docs/TRUSTED.md declares {sorted(found)} but this script knows "
              f"{sorted(declared)} -- the trusted base and its checker have drifted apart",
              file=sys.stderr)
        return None
    return found


def closure(start: pathlib.Path, corpus_root: pathlib.Path):
    """every file transitively included by `start`.

    TPTP RESOLVES AN INCLUDE AGAINST THE PROVER'S WORKING DIRECTORY, NOT THE INCLUDING FILE, and
    that difference is not academic -- it is how three negative controls came to be unreadable for a
    whole round.  `proofs/unbounded/run.sh` runs the negative controls with `cd negative`, so a
    control in that subdirectory that includes the shared signature by its BARE name resolves it
    inside the subdirectory, where it is not -- rather than one level up, where it is.  Vampire
    reported a user error, emitted no SZS status, and the harness scored the non-answer as
    "NOT-PROVED (expected)": a pass for a control that pinned nothing.

    So this resolves the includer-relative path (which is what a reader assumes) and, failing that,
    the corpus root -- and reports the second case as FRAGILE rather than silently accepting it,
    because whether it works depends on where the prover was invoked from."""
    seen, stack = set(), [start]
    missing, fragile, reasserted = set(), set(), set()
    while stack:
        f = stack.pop()
        try:
            text = f.read_text()
        except OSError:
            missing.add(str(f.name))
            continue
        # follow the re-asserted-lemma edge as well as the includes: a consumer of a re-asserted
        # lemma depends on whatever the DISCHARGING theorem depends on
        for dis in DISCHARGED_BY.findall(text):
            tgt = (f.parent / dis).resolve()
            reasserted.add(f"{f.name} re-asserts a lemma discharged by {dis}")
            if tgt not in seen:
                seen.add(tgt)
                stack.append(tgt)
        for inc in INCLUDE.findall(text):
            tgt = (f.parent / inc).resolve()
            if not tgt.is_file():
                alt = (corpus_root / inc).resolve()
                if alt.is_file():
                    fragile.add(f"{f.name} includes '{inc}', which resolves only from the corpus "
                                f"root -- it depends on the prover's working directory")
                    tgt = alt
            if tgt in seen:
                continue
            seen.add(tgt)
            stack.append(tgt)
    return seen, missing, fragile, reasserted


def classify(status_file: pathlib.Path, corpus: str, kind: str = "tptp"):
    """one row per reported status, with its closure's intersection with the trusted base"""
    rows = []
    corpus_wide = sorted(k for k, v in TRUSTED.items() if v.get("corpus") == corpus)
    for line in status_file.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        name, verdict = parts[0].strip(), parts[-1].strip()
        # A COLUMN HEADER IS NOT A STATUS.  `proofs/pipeline/fixpoint-gate/STATUS.tsv` carries
        # `file  z3  vampire  expected  verdict`, and reading it as a row reports a status for a
        # file called "file".
        if name in ("file", "obligation", "name") and verdict in ("verdict", "status"):
            continue
        # a negative control is not a claim; it is the check that the corpus is not vacuous
        negative = verdict.startswith("NOT-PROVED")
        # THE OBLIGATION FILE, resolved by the table's kind: `.p` beside a TPTP table (or under
        # `negative/`), `.smt2` beside an SMT one.  Appending `.p` to an SMT row name -- which an
        # earlier revision did -- reports every one of the 240 SMT statuses as having no proof file.
        ext = ".p" if kind == "tptp" else ".smt2"
        p = status_file.parent / (name if name.endswith(ext) else name + ext)
        if not p.is_file() and kind == "tptp":
            alt = status_file.parent / "negative" / (name + ext)
            p = alt if alt.is_file() else p
        if kind == "tptp":
            cl, missing, fragile, reasserted = closure(p, status_file.parent)
        else:
            cl, missing, fragile, reasserted = set(), set(), set(), set()
        # ------------------------------------------------------------------------------------------
        # `% MECHANIZED-IN:` MARKERS, ATTRIBUTED PER TRUSTED ENTRY.
        #
        # A MARKER DISCHARGES THE ENTRY ITS OWN FILE ASSERTS, AND NOTHING ELSE.  The first version of
        # this dropped EVERY reached entry as soon as any marker in the closure was witnessed, and the
        # self-test caught it immediately: one marker naming the wrap-roundtrip theorem reported
        # `card_wrap  discharges T1,T7`, when T7 is the counting axiom module `_card.p` and the Lean
        # theorem says nothing whatever about counting.  That is precisely the lenient direction this
        # script exists to close, arriving through the mechanism meant to close it.
        #
        # So attribution is by FILE: a marker in the file that IS a trusted entry's axiom module
        # (`TRUSTED[T]["axiom"]`) discharges that entry; a marker in the obligation file itself
        # discharges an entry whose `rows` name that obligation (T2's four induction principles are
        # asserted inside `fixpoint_is_lfp.smt2`, so that is where its marker belongs).  A marker
        # anywhere else discharges nothing and is reported as ORPHANED -- `_cancel.p`, for instance,
        # only RE-ASSERTS a lemma and already carries a `% DISCHARGED-BY:` edge; the schema it
        # ultimately rests on lives in `_path_induction.p`, and that is the file a lift must mark.
        # ------------------------------------------------------------------------------------------
        mech_for = {}        # trusted entry -> the markers whose file asserts it
        orphan_mech = []     # markers in files that assert no trusted entry
        for f in ([p] + sorted(cl, key=lambda x: x.name)):
            try:
                markers = [f"{a}#{b}" for a, b in MECHANIZED_IN.findall(f.read_text())]
            except OSError:
                continue
            if not markers:
                continue
            owned = [k for k, v in TRUSTED.items() if v["axiom"] and v["axiom"] == f.name]
            if f == p:
                owned += [k for k, v in TRUSTED.items()
                          if name in v.get("rows", ()) or name.removesuffix(ext) in v.get("rows", ())]
            if not owned:
                orphan_mech += [f"{m} (in {f.name}, which asserts no trusted entry)" for m in markers]
            for k in sorted(set(owned)):
                mech_for.setdefault(k, []).extend(markers)
        names = {c.name for c in cl}
        reached = sorted(k for k, v in TRUSTED.items() if v["axiom"] and v["axiom"] in names)
        # the DIRECT, file-scoped entries: a trusted principle asserted inside this very obligation
        direct = sorted(k for k, v in TRUSTED.items()
                        if name in v.get("rows", ()) or name.removesuffix(".smt2") in v.get("rows", ()))
        reached = sorted(set(reached) | set(direct))
        # THE LIFT, per entry.  An entry is dropped from `reached` only when EVERY marker offered for
        # it is WITNESSED as built and sorry-free by `scripts/check_lean.sh`.  With no witness (the
        # Lean gate was not run on this machine) nothing is dropped.
        witness = read_lean_witness()
        lifted, mechanized, claimed = [], [], []
        for k in sorted(set(reached)):
            ms = sorted(set(mech_for.get(k, ())))
            if not ms:
                continue
            claimed += [f"{k} via {m}" for m in ms]
            if all(m in witness for m in ms):
                lifted.append(k)
                mechanized += ms
        reached = sorted(set(reached) - set(lifted))
        mechanized = sorted(set(mechanized))
        rows.append(dict(name=name, verdict=verdict, negative=negative, reached=reached,
                         corpus=corpus_wide, deps=len(cl), missing=sorted(missing),
                         fragile=sorted(fragile), reasserted=sorted(reasserted),
                         exists=p.is_file(), mechanized=mechanized, lifted=sorted(lifted),
                         mech_claimed=sorted(set(claimed)), orphan_mech=sorted(set(orphan_mech))))
    return rows


def annotate():
    """rewrite each status table's verdict column so a conditional result says so.

    WHY THE TABLE AND NOT JUST THE REPORT.  `run.sh` writes the verdict the prover reached, and it
    is right to: the prover is what ran.  But "PROVED" in a table is read as unqualified, and for a
    result whose closure reaches an admitted schema that reading is wrong.  Duplicating the trusted
    base into `run.sh` so it could annotate as it goes would give two copies to drift apart, so the
    annotation is applied HERE, from the one list, after the run -- and `--check` then holds the
    table to it.

    The rewrite is idempotent and only ever WEAKENS a verdict; it never turns an OPEN into a
    PROVED, and it leaves negative controls alone."""
    # EVERY TABLE, NOT JUST THE TPTP ONE.  An earlier revision skipped the SMT tables on the ground
    # that their harnesses own the files -- but that left `terminating/STATUS.tsv` reporting
    # `fixpoint_is_lfp` as unqualified PROVED while T2's four induction principles are asserted
    # INSIDE THAT FILE, which is precisely the state the requirement forbids.  Ownership is not a
    # reason to leave a status wrong; it is a reason for the owning harness to call this script,
    # which `proofs/run.sh` and `terminating/run.sh` now do.  Only rows this analysis can DECIDE are
    # touched, and the rewrite only ever weakens a verdict.
    for status, corpus, kind in STATUS_TABLES:
        if not status.is_file():
            continue
        rows = classify(status, corpus, kind)
        by_name = {r["name"]: r for r in rows}
        out, changed = [], 0
        for line in status.read_text().splitlines():
            if not line.strip() or line.startswith("#"):
                out.append(line)
                continue
            parts = line.split("\t")
            r = by_name.get(parts[0].strip())
            # REWRITE ANY `PROVED*` VERDICT TO THE COMPUTED ONE, not only a bare `PROVED`.  An
            # earlier revision matched `== "PROVED"` exactly, so once a row had been annotated it
            # could never be CORRECTED -- and `card_wrap` needed correcting from `T1` to `T1,T7`
            # the moment T7 was declared.  This still only ever weakens: `reached` is what the
            # closure found, and a row with nothing reached is left alone.
            # A LIFTED ROW SAYS WHAT LIFTED IT.  Writing a bare `PROVED` would erase the only
            # trace of why the qualification went away, and the next reader could not tell a row
            # that never needed one from a row a Lean theorem discharged.
            if r and r.get("mechanized") and r.get("lifted"):
                want = ("PROVED (MECHANIZED " + ",".join(r["mechanized"]) +
                        " discharges " + ",".join(r["lifted"]) + ")")
            else:
                want = "PROVED-MODULO " + ",".join(r["reached"]) if r and r["reached"] else None
            if (r and not r["negative"] and want
                    and parts[-1].strip().startswith("PROVED")
                    and parts[-1].strip() != want):
                parts[-1] = want
                changed += 1
            out.append("\t".join(parts))
        if changed:
            # ATOMIC, for the same reason the run.sh drivers stage their tables: this rewrite is the
            # LAST writer of a file four other tools read, and a `write_text` that is interrupted
            # between truncate and write leaves the committed table empty -- losing a corpus that
            # took tens of minutes of prover time to produce, with no way to tell an emptied table
            # from a corpus that certifies nothing.
            tmp = status.with_suffix(status.suffix + ".tmp")
            tmp.write_text("\n".join(out) + "\n")
            tmp.replace(status)
            print(f"annotated {changed} conditional verdict(s) in {status.relative_to(ROOT)}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true",
                    help="exit non-zero if any unqualified PROVED has a conditional closure")
    ap.add_argument("--annotate", action="store_true",
                    help="rewrite the status tables so a conditional result SAYS it is conditional, "
                         "then re-check.  This is what makes the requirement enforceable: the "
                         "prover writes the verdict it reached, and the closure is what decides "
                         "whether that verdict is unqualified")
    a = ap.parse_args()

    known = read_trusted_ids()
    if known is None:
        sys.exit(2)

    if a.annotate:
        annotate()

    problems = []

    # EVERY DECLARED ASSUMPTION MUST BE A DECLARED ASSUMPTION.  This is the check that turns
    # docs/TRUSTED.md's "complete list" from a sentence into an invariant.
    undeclared = []
    for f in sorted(ROOT.glob("proofs/**/*.p")):
        text = f.read_text(errors="replace")
        if not ASSUMED_BLOCK.search(text):
            continue
        entries = TRUSTED_ENTRY.findall(text)
        if not entries:
            undeclared.append(f"{f.relative_to(ROOT)}: declares an ASSUMED block but names no "
                              "`% TRUSTED-ENTRY: T<n>` -- so it assumes something docs/TRUSTED.md "
                              "does not list, and that file claims to list everything")
        for e in entries:
            if e not in known:
                undeclared.append(f"{f.relative_to(ROOT)}: names `{e}`, which docs/TRUSTED.md does "
                                  "not define")
    problems += undeclared
    print("THE DEPENDENCY CLOSURE OF EVERY REPORTED STATUS")
    print("=" * 100)
    total_reported = 0
    for status, corpus, kind in STATUS_TABLES:
        if not status.is_file():
            problems.append(f"{status.relative_to(ROOT)}: declared as a status table but missing")
            continue
        rows = classify(status, corpus, kind)
        total_reported += len(rows)
        pos = [r for r in rows if not r["negative"]]
        cond = [r for r in pos if r["reached"]]
        print(f"\n{status.relative_to(ROOT)}  [{kind}]  --  {len(rows)} reported, "
              f"{len(pos)} positive claims, {len(rows) - len(pos)} negative controls")
        if kind != "tptp":
            print("  include-closure does NOT apply: an SMT obligation carries its axioms inline, so "
                  "dependency here is not inclusion.  Classified by the DECLARED trusted entries "
                  "that apply to this corpus; verdicts are NOT rewritten from here.")
            print("  SO THIS TABLE'S COVERAGE IS WEAKER, and saying which way matters: a row is "
                  "flagged when a trusted entry NAMES it, and a dependency that is neither named "
                  "nor an include is invisible here.  Closing that needs an assert-level analysis "
                  "of the SMT obligations, which this script does not attempt.")
        print(f"  corpus-wide trusted entries for `{corpus}`: "
              f"{', '.join(rows[0]['corpus']) if rows else '-'}  "
              "(declared for the tier, not reachable through any include)")
        how = ("reach a trusted AXIOM through their includes" if kind == "tptp"
               else "are conditional on a DECLARED, file-scoped trusted entry")
        print(f"  {len(cond)} of {len(pos)} positive claims {how}:")
        for r in cond:
            names = ", ".join(f"{k} ({TRUSTED[k]['what']})" for k in r["reached"])
            print(f"    {r['name']:34s} {r['verdict']:12s} PROVED-MODULO {names}")
            want = "PROVED-MODULO " + ",".join(r["reached"])
            why = ("its include closure reaches" if kind == "tptp"
                   else "a declared trusted entry names it:")
            if r["verdict"] == "PROVED":
                problems.append(f"{r['name']}: reported as unqualified PROVED, but {why} "
                                f"{', '.join(r['reached'])} -- it is CONDITIONAL. "
                                f"`--annotate` rewrites it to `{want}`.")
            elif r["verdict"] != want:
                problems.append(f"{r['name']}: reported as `{r['verdict']}` but its closure says "
                                f"`{want}`")
        # --- the Lean lifts, and the markers that could not be honoured (plan.md 0.5) ------------
        mech = [r for r in rows if r.get("mechanized")]
        unwitnessed = [r for r in rows
                       if r.get("mech_claimed") and not r.get("mechanized")]
        if mech:
            print(f"  {len(mech)} claim(s) LIFTED to unqualified PROVED by a witnessed Lean theorem:")
            for r in mech:
                print(f"    {r['name']:34s} discharges {','.join(r['lifted']) or '-'} "
                      f"via {','.join(r['mechanized'])}")
        orphans = sorted({o for r in rows for o in r.get("orphan_mech", ())})
        if orphans:
            print(f"  {len(orphans)} ORPHANED `% MECHANIZED-IN:` marker(s) -- they discharge NOTHING, "
                  "because a marker only discharges the trusted entry its own file asserts:")
            for o in orphans:
                print(f"    {o}")
            problems += [f"orphaned `% MECHANIZED-IN:` marker: {o} -- move it to the file that "
                         "asserts the entry it is meant to discharge, or delete it" for o in orphans]
        if unwitnessed:
            # NOT A PROBLEM, AND SAYING WHY MATTERS.  A marker with no witness means the Lean gate
            # was not run on this machine, so the row stays reported as CONDITIONAL -- the
            # conservative direction.  It is printed because a reader looking at a
            # `PROVED-MODULO T1` row that carries a marker deserves to know the lift exists and
            # what to run for it, rather than concluding the marker was ignored.
            print(f"  {len(unwitnessed)} claim(s) carry a `% MECHANIZED-IN:` marker with NO local "
                  "witness, so they stay CONDITIONAL (run `scripts/check_lean.sh`):")
            for r in unwitnessed:
                print(f"    {r['name']:34s} claims {','.join(r['mech_claimed'])}")
        unresolved = [r for r in rows if not r["exists"]]
        if unresolved:
            print(f"  {len(unresolved)} reported status(es) have no proof file: "
                  + ", ".join(r["name"] for r in unresolved[:8]))
            problems += [f"{r['name']}: a status is reported for a file that does not exist"
                         for r in unresolved]
        missing = sorted({m for r in rows for m in r["missing"]})
        if missing:
            print(f"  unresolvable includes: {', '.join(missing)}")
            problems += [f"unresolvable include `{m}`" for m in missing]
        # A RE-ASSERTED LEMMA MUST ITSELF BE PROVED.  Following the edge fixes the closure; it does
        # not license the re-assertion.  An axiom file asserting a clause whose named discharging
        # theorem is OPEN, or absent from the table, is a worse defect than the missed conditional
        # this edge was added to catch -- so it is checked here rather than trusted.
        verdicts = {r["name"]: r["verdict"] for r in rows}
        for r in rows:
            for m in r["reasserted"]:
                thm = m.rsplit(" ", 1)[-1].removesuffix(".p")
                v = verdicts.get(thm)
                if v is None:
                    problems.append(f"{m}: `{thm}` is not in {status_file.name}, so the "
                                    "re-assertion rests on nothing this corpus reports")
                elif not v.startswith("PROVED"):
                    problems.append(f"{m}: `{thm}` is reported `{v}`, so the re-asserted clause is "
                                    "NOT a proved lemma")
        rea = sorted({m for r in rows for m in r["reasserted"]})
        if rea:
            print(f"  {len(rea)} re-asserted-lemma edge(s) followed (an `include` graph alone would "
                  "stop at the re-assertion):")
            for m in rea:
                print(f"    {m}")
        fragile = sorted({m for r in rows for m in r["fragile"]})
        if fragile:
            print(f"  {len(fragile)} include(s) resolve ONLY from the corpus root:")
            for m in fragile:
                print(f"    {m}")
            problems += [f"working-directory-dependent include: {m}" for m in fragile]
        depth = max((r["deps"] for r in rows), default=0)
        print(f"  deepest closure: {depth} axiom file(s)")

    print("\n" + "=" * 100)
    print(f"ENUMERATED: {total_reported} reported statuses across {len(STATUS_TABLES)} tables.")
    print(f"ASSUMED-BLOCK DECLARATIONS: {'all named a T entry' if not undeclared else str(len(undeclared)) + ' undeclared'}")
    print("WHAT THIS CANNOT SEE, stated so the report is not read as complete:")
    for k, v in sorted(TRUSTED.items()):
        if v["axiom"] is None:
            print(f"  {k}  {v['what']}")
            print(f"      not reachable through an `include`; it is a property of the "
                  f"`{v.get('corpus', '?')}` corpus or of the implementation, so no closure "
                  "computed here can discharge or detect it.")

    if problems:
        print(f"\n{len(problems)} PROBLEM(S):")
        for pb in problems:
            print(f"  {pb}")
    else:
        print("\nevery reported status is consistent with its closure")
    sys.exit(1 if (problems and a.check) else 0)


if __name__ == "__main__":
    main()
