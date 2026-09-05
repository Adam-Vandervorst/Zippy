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
               what="the whistle terminates (Kruskal's tree theorem) -- MECHANIZED per run in Whistle.lean; "
                    "a run outside the covered alphabet is bounded by the Deadline and reported, not assumed"),
    "T4": dict(axiom=None, corpus="pipeline", what="EquivPipeline.expand, the stage-0 expansion"),
    "T5": dict(axiom=None, corpus="unbounded",
               what="Range is outside the certified pointwise algebra"),
    "T6": dict(axiom=None, corpus="unbounded", what="grounded functions are deterministic"),
    "T7": dict(axiom="_card.p", what="the counting axioms (4 counting + injective-image + pfxmap)"),
    # 2E.4: the SMT tiers' bridging induction over the chain index (`; ASSUMED: T8` markers)
    "T8": dict(axiom=None, what="induction over the natural-number chain index, asserted after base and step"),
    # A6: the instrumented executors ARE the operational semantics the resource analysis bounds; the
    # compositional event semantics is checked against them differentially (SpatialSemanticsCheck), not proved
    "T9": dict(axiom=None, corpus="spatial-transfers",
               what="the counted executors are the event semantics (checked differentially by SpatialSemanticsCheck, A1)"),
}

# ==================================================================================================
# A6: THE TRANSFER RULES OF THE RESOURCE ANALYSIS.  proofs/spatial/REGISTRY.tsv names every rule and
# what discharges it (a Lean theorem in proofs/lean/Zippy/Spatial.lean, the independent checker
# proofs/spatial/check_transfers.py, a differential gate suite, or a stated premise);
# proofs/spatial/STATUS.tsv is the checker's verdict table.  A cost result is labelled certified
# (`CostReport.certified`) only when every rule its derivation used is PROVED there — so `--check`
# refuses an OPEN row, a registry row without a status, or a status row the registry does not know.
# ==================================================================================================
SPATIAL_REGISTRY = ROOT / "proofs/spatial/REGISTRY.tsv"
SPATIAL_STATUS = ROOT / "proofs/spatial/STATUS.tsv"


# ==================================================================================================
# ONE DEPENDENCY GRAPH OVER THE TYPED PROOF TRACES. A pipeline cell's claim is its trace
# (proofs/pipeline/traces/<cell>.trace.tsv); every leaf names what it rests on — a law
# (proofs/laws/REGISTRY.tsv, whose certificates have rows in proofs/STATUS.tsv), a backend artifact
# (proofs/pipeline/STATUS.tsv verdict + its `; TRUSTS:` header of T/O ids), the substitution and fold
# theorems (terminating/REGISTRY.tsv O6a/O12b), a mechanized boundary theorem.  This traverses them
# as ONE graph, classifies every trace UNCONDITIONAL / CONDITIONAL (with its MINIMAL open set) /
# FAILED (a leaf that resolves to nothing), refuses cycles in the law-certificate include graph, and
# writes target/trace-closure.tsv for the acceptance generator (E3).  `--inject-open ID` marks a
# registry row open for one run, which must turn every transitive consumer conditional (C4's
# acceptance) — a mutation of the graph, not of the tree.
# ==================================================================================================
TRACE_DIR = ROOT / "proofs/pipeline/traces"
TRACE_CLOSURE = ROOT / "target" / "trace-closure.tsv"

def read_tsv_rows(path, skip_header_prefixes=("#",)):
    if not path.is_file():
        return []
    out = []
    for line in path.read_text(errors="replace").splitlines():
        if not line.strip() or any(line.startswith(p) for p in skip_header_prefixes):
            continue
        out.append(line.split("\t"))
    return out

def registry_kinds():
    """id -> kind for terminating/REGISTRY.tsv"""
    return {cols[0]: cols[1] for cols in read_tsv_rows(ROOT / "terminating/REGISTRY.tsv") if len(cols) > 1 and cols[0] != "id"}

def law_rows():
    """law -> (kind, certificates) for proofs/laws/REGISTRY.tsv"""
    out = {}
    for cols in read_tsv_rows(ROOT / "proofs/laws/REGISTRY.tsv"):
        if len(cols) >= 3 and cols[0] != "law":
            out[cols[0]] = (cols[1], cols[2])
    return out

def status_verdicts(path):
    """name(stem) -> verdict (last column)"""
    out = {}
    for cols in read_tsv_rows(path):
        if len(cols) >= 2:
            name = cols[0].split("/")[-1]
            if name.endswith((".smt2", ".p", ".egg")):
                name = name.rsplit(".", 1)[0]
            out[name] = cols[-1].strip()
    return out

TRUSTS_HEADER = re.compile(r"^\s*[;%]\s*TRUSTS:\s*(.*)$", re.M)

def artifact_trusts(rel):
    f = ROOT / rel
    if not f.is_file():
        return None
    m = TRUSTS_HEADER.search(f.read_text(errors="replace"))
    if not m:
        return []
    body = m.group(1).strip()
    return [] if body == "-" else [t.strip() for t in body.split(",") if t.strip()]

def include_cycles(corpus_root):
    """cycles in the include graph of a corpus (a certificate may not rest on itself)"""
    edges = {}
    for f in sorted(corpus_root.glob("*.smt2")) + sorted(corpus_root.glob("*.p")):
        try: text = f.read_text(errors="replace")
        except OSError: continue
        edges[f.name] = [inc.split("/")[-1] for inc in INCLUDE.findall(text)]
    cycles = []
    state = {}
    def dfs(n, stack):
        state[n] = 1; stack.append(n)
        for m in edges.get(n, []):
            if state.get(m) == 1:
                cycles.append(" -> ".join(stack[stack.index(m):] + [m]))
            elif state.get(m) is None:
                dfs(m, stack)
        stack.pop(); state[n] = 2
    for n in edges:
        if state.get(n) is None: dfs(n, [])
    return cycles

def resolve_dep(dep, kinds, laws, law_status, term_status, lean_witness, injected):
    """one dependency token -> (status, detail) with status in DISCHARGED / CONDITIONAL / OPEN / FAILED"""
    if dep in injected:
        return "OPEN", f"{dep} (injected open)"
    if dep.startswith("law:"):
        name = dep[4:]
        if name == "zipper-refinement":
            return "DISCHARGED", "zipper_refinement.smt2 + Zipper.lean"
        if name not in laws:
            return "FAILED", f"law {name} has no registry row"
        kind, certs = laws[name]
        if kind == "DEFINITIONAL":
            return "DISCHARGED", f"law {name}: definitional"
        # FILE / SCHEMATIC / GROUND: every certificate must be PROVED in proofs/STATUS.tsv (a GROUND law's
        # certificates are the per-operation implementation theorems, `threeway_*` / `impl_*`)
        opens = []
        for c in certs.split(","):
            stem = c.strip().split("/")[-1].rsplit(".", 1)[0].replace("*", "")
            if not stem: continue
            wild = "*" in c
            matches = [v for k, v in law_status.items() if k == stem or (wild and k.startswith(stem))]
            if not matches:
                opens.append(f"{stem}: no status row")
            for v in matches:
                if not v.startswith("PROVED"):
                    opens.append(f"{stem}: {v}")
                elif "PROVED-MODULO" in v:
                    opens.append(f"{stem}: {v}")
        if not opens:
            return "DISCHARGED", f"law {name}: {certs}"
        if all("MODULO" in o for o in opens):
            return "CONDITIONAL", f"law {name}: " + "; ".join(opens)
        return "OPEN", f"law {name}: " + "; ".join(opens)
    if re.fullmatch(r"O\d+[a-z]?(-[A-Z]+)?", dep):
        kind = kinds.get(dep)
        if kind is None:
            return "FAILED", f"{dep}: no registry row"
        if kind.startswith("MECHANIZED"):
            return "DISCHARGED", f"{dep}: {kind[:40]}"
        if kind.startswith("OPEN"):
            return "OPEN", f"{dep}: {kind[:40]}"
        if kind == "FILE":
            return "DISCHARGED", f"{dep}: FILE"
        return "CONDITIONAL", f"{dep}: {kind[:40]} (evidence, not a theorem)"
    if re.fullmatch(r"T\d+", dep):
        if dep not in TRUSTED:
            return "FAILED", f"{dep}: not in docs/TRUSTED.md"
        mech = entry_mechanizations().get(dep, [])
        if mech and all(m in lean_witness for m in mech):
            return "DISCHARGED", f"{dep}: mechanized ({len(mech)} theorem(s))"
        return "CONDITIONAL", f"{dep}: trusted base entry"
    if dep.startswith("outside:"):
        return "CONDITIONAL", dep
    return "FAILED", f"unknown dependency token {dep}"

def check_trace_closure(problems, check, injected):
    print(f"\n{TRACE_DIR.relative_to(ROOT)}  [typed proof traces, one dependency graph — C3/C4]")
    if not TRACE_DIR.is_dir():
        problems.append("proofs/pipeline/traces is missing (run `sbt \"testOnly morkl.EquivPipelineTest\"`)")
        return
    kinds = registry_kinds(); laws = law_rows()
    law_status = status_verdicts(ROOT / "proofs/STATUS.tsv")
    term_status = status_verdicts(ROOT / "terminating/STATUS.tsv")
    cell_status = status_verdicts(ROOT / "proofs/pipeline/STATUS.tsv")
    lean_witness = read_lean_witness()
    for cyc in include_cycles(ROOT / "proofs/laws") + include_cycles(ROOT / "proofs"):
        problems.append(f"cycle in the certificate include graph: {cyc}")
    rows = []
    for f in sorted(TRACE_DIR.glob("*.trace.tsv")):
        cell = f.name.removesuffix(".trace.tsv")
        deps = []   # dependency tokens the leaves name
        for line in f.read_text(errors="replace").splitlines():
            if not line.strip() or line.startswith("#") or line.startswith("T\t"):
                continue
            cols = line.split("\t")
            if len(cols) < 6: continue
            kind, fields = cols[1], cols[4]
            fd = dict(kv.split("=", 1) for kv in fields.split(";") if "=" in kv) if fields != "-" else {}
            if kind == "LawInstance":
                deps.append("law:" + fd.get("law", "?"))
            elif kind in ("Unfold",):
                deps.append("O6a")
            elif kind in ("Fold", "Generalization"):
                deps.append("O12b"); deps.append("O6a")
            elif kind == "BackendRefinement":
                art = fd.get("artifact", "")
                deps.append("artifact:" + art)
                ts = artifact_trusts(art)
                if ts is None:
                    deps.append("missing:" + art)
                else:
                    deps.extend(ts)
            elif kind == "GraphOptimizerNoOp":
                deps.append("T4")
        # resolve
        opens, conds, failed, discharged = [], [], [], []
        for d in sorted(set(deps)):
            if d.startswith("artifact:"):
                art = d[len("artifact:"):]
                stem = art.split("/")[-1].rsplit(".", 1)[0]
                if art == "proofs/zipper_refinement.smt2":
                    v = law_status.get("zipper_refinement", "?")
                else:
                    v = cell_status.get(stem, "?")
                if v.startswith("PROVED") and "MODULO" not in v or v == "LAW-JUSTIFIED":
                    discharged.append(f"{stem}: {v}")
                elif v.startswith("PROVED-MODULO") or v.startswith("LAW-JUSTIFIED"):
                    conds.append(f"{stem}: {v}")
                elif v in ("TRIVIAL", "IDENTICAL-STRUCTURE"):
                    conds.append(f"{stem}: marker {v} cited as an obligation")
                else:
                    failed.append(f"{stem}: {v}")
                continue
            if d.startswith("missing:"):
                failed.append(d); continue
            st, detail = resolve_dep(d, kinds, laws, law_status, term_status, lean_witness, injected)
            {"DISCHARGED": discharged, "CONDITIONAL": conds, "OPEN": opens, "FAILED": failed}[st].append(detail)
        status = "FAILED" if failed else "OPEN" if opens else "CONDITIONAL" if conds else "UNCONDITIONAL"
        minimal = opens + conds + failed
        rows.append((cell, status, len(deps), minimal))
        verdict = cell_status.get(cell, "?")
        if check and status in ("OPEN", "FAILED") and verdict.startswith(("PROVED", "LAW-JUSTIFIED")) and "MODULO" not in verdict:
            problems.append(f"{cell}: reported `{verdict}` but its trace closure is {status}: {'; '.join(minimal[:3])}")
        if check and status == "FAILED":
            problems.append(f"{cell}: a trace leaf resolves to nothing: {'; '.join(failed[:3])}")
    # an INJECTION run must not overwrite the real closure (check_coverage.py and gen_acceptance.py read it):
    # its rows go to a sibling file
    out_path = TRACE_CLOSURE if not injected else TRACE_CLOSURE.with_name("trace-closure-injected.tsv")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w") as out:
        out.write("# cell\tstatus\tdependencies\tminimal-open-set\n")
        for cell, status, n, minimal in rows:
            out.write(f"{cell}\t{status}\t{n}\t{' | '.join(minimal) if minimal else '-'}\n")
    for cell, status, n, minimal in rows:
        print(f"    {cell:34s} {status:14s} {n:3d} dep(s)  {('; '.join(minimal))[:110]}")
    by = {}
    for _, st, _, _ in rows: by[st] = by.get(st, 0) + 1
    print(f"  {len(rows)} traces: " + ", ".join(f"{k} {v}" for k, v in sorted(by.items())) + f"; closure written to {out_path.relative_to(ROOT)}")
    if injected:
        affected = [c for c, st, _, mn in rows if any("injected open" in m for m in mn)]
        print(f"  INJECTED OPEN {sorted(injected)}: {len(affected)} consumer trace(s) turned OPEN")
        return affected
    return None


def check_spatial_transfers(problems):
    """the A6 transfer table: every registry rule has a verdict and none is OPEN"""
    print(f"\n{SPATIAL_REGISTRY.relative_to(ROOT)}  [transfer rules of the resource analysis, A6]")
    if not SPATIAL_REGISTRY.is_file():
        problems.append("proofs/spatial/REGISTRY.tsv is missing"); return
    reg = {}
    for line in SPATIAL_REGISTRY.read_text().splitlines():
        if not line.strip() or line.startswith("#"): continue
        cols = line.split("\t")
        reg[cols[0]] = cols[1]
    if not SPATIAL_STATUS.is_file():
        problems.append("proofs/spatial/STATUS.tsv is missing: run proofs/spatial/check_transfers.py "
                        "(after `sbt \"testOnly morkl.SpatialTransferDump\"`); no cost result is certified without it")
        print(f"  {len(reg)} rules registered, NO verdict table")
        return
    st = {}
    for line in SPATIAL_STATUS.read_text().splitlines():
        if not line.strip() or line.startswith("#"): continue
        cols = line.split("\t")
        st[cols[0]] = cols[-1].strip()
    kinds = {}
    for rid, kind in reg.items():
        v = st.get(rid)
        if v is None:
            problems.append(f"{rid}: registered transfer rule with no verdict in proofs/spatial/STATUS.tsv")
        elif v == "OPEN":
            problems.append(f"{rid}: transfer rule OPEN -- no cost result depending on it may be labelled certified")
        kinds[kind.split(" ")[0]] = kinds.get(kind.split(" ")[0], 0) + 1
    for rid in st:
        if rid not in reg:
            problems.append(f"{rid}: a verdict for a transfer rule the registry does not know")
    for rid, v in sorted(st.items()):
        print(f"    {rid:24s} {reg.get(rid, '?'):14s} {v}")
    print(f"  {len(reg)} rules: " + ", ".join(f"{k} {n}" for k, n in sorted(kinds.items())) +
          f"; {sum(1 for v in st.values() if v == 'OPEN')} OPEN")


# ---------------------------------------------------------------------------------------------
# ENTRY-LEVEL MECHANIZATION.  docs/TRUSTED.md may carry, inside an entry's section,
#     MECHANIZED-IN: proofs/lean/Zippy/<File>.lean#<Theorem>
# naming the Lean theorem that IS that entry's schema (T1's `path_induction` is the schema for every
# predicate, not one conclusion).  When `scripts/check_lean.sh` has witnessed every such theorem as
# built and sorry-free, the entry is discharged for EVERY row that reaches it -- through an include,
# through a `; ASSUMED:` marker, or through a `rows` declaration -- which is what lets the 115 SMT
# obligations that assert the datatype-induction schema stop being conditional at once, instead of
# needing 115 per-file markers pointing at one theorem.
# ---------------------------------------------------------------------------------------------
ENTRY_MECH = re.compile(r"^MECHANIZED-IN:\s*([^\s`<>|]+)#([^\s`<>|]+)", re.M)


def entry_mechanizations():
    """{T -> [marker...]} from docs/TRUSTED.md's per-entry MECHANIZED-IN lines"""
    text = (ROOT / "docs/TRUSTED.md").read_text()
    out = {}
    cur = None
    for line in text.splitlines():
        m = re.match(r"^## (T\d+)\.", line)
        if m:
            cur = m.group(1); continue
        m = ENTRY_MECH.match(line)
        if m and cur:
            out.setdefault(cur, []).append(f"{m.group(1)}#{m.group(2)}")
    return out


ASSERT_CLOSURE = ROOT / "target" / "assert-closure.tsv"


def read_assert_closure():
    """{repo-relative .smt2 path -> set of T ids} written by scripts/check_asserts.py (2E.4); an
    absent table is an EMPTY mapping, and `--check` reports it, because with it absent an SMT row's
    dependencies are invisible again."""
    out = {}
    if not ASSERT_CLOSURE.is_file():
        return None
    for line in ASSERT_CLOSURE.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        f, ts = line.split("\t")
        out[f] = set() if ts.strip() == "-" else set(ts.split(","))
    return out

# THE MARKER THAT MAKES docs/TRUSTED.md's COMPLETENESS CLAIM CHECKABLE.  An axiom file that declares
# an `% ASSUMED` block is asserting something the corpus does not derive, and that is exactly what a
# T entry is for -- so it must name one.  The check exists because the claim was already false:
# `_card.p` declared six assumed counting axioms in its own header and none was a T entry, and
# `card_wrap` was reported as unqualified PROVED on top of them.
ASSUMED_BLOCK = re.compile(r"^%\s*ASSUMED\b", re.M)
TRUSTED_ENTRY = re.compile(r"^%\s*TRUSTED-ENTRY:\s*(T\d+)", re.M)

# ==================================================================================================
# THE MARKER THAT DISCHARGES A TRUSTED ENTRY, RATHER THAN DECLARING ONE.
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
TRUSTS_RE = re.compile(r"^\s*[;%]\s*TRUSTS:\s*(.*)$", re.M)
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
        # `; TRUSTS:` (0.8 / 2E.5): an emitted artifact declares what its claim rests on.  T entries
        # join `reached`; open rows and outside constructs are gaps, reported in the verdict as
        # `PROVED-MODULO O6a` / `PROVED-MODULO outside:Range` (the emitter's `Certified.qualify`
        # already writes them that way; this is the reader's side of the same contract).
        gaps = []
        if kind != "tptp" and p.is_file():
            mt = TRUSTS_RE.search(p.read_text())
            if mt:
                for tok in [t.strip() for t in mt.group(1).split(",") if t.strip() and t.strip() != "-"]:
                    if re.fullmatch(r"T\d+", tok):
                        reached = sorted(set(reached) | {tok})
                    elif re.fullmatch(r"O\d+[a-z]?|outside:[A-Za-z0-9_-]+", tok):
                        gaps.append(tok)
        # THE ASSERT-LEVEL CLOSURE (2E.4): for an SMT obligation, the trusted entries its own
        # `; ASSUMED:` markers name, transitively through its `; DERIVED-FROM:` edges, as computed
        # by scripts/check_asserts.py.  This is the SMT twin of the include closure above.
        if kind != "tptp":
            ac = read_assert_closure()
            if ac is not None:
                rel = str(p.resolve().relative_to(ROOT)) if p.is_file() else None
                if rel in ac:
                    reached = sorted(set(reached) | ac[rel])
        # the DIRECT, file-scoped entries: a trusted principle asserted inside this very obligation
        direct = sorted(k for k, v in TRUSTED.items()
                        if name in v.get("rows", ()) or name.removesuffix(".smt2") in v.get("rows", ()))
        reached = sorted(set(reached) | set(direct))
        # THE LIFT, per entry.  An entry is dropped from `reached` only when EVERY marker offered for
        # it is WITNESSED as built and sorry-free by `scripts/check_lean.sh`.  With no witness (the
        # Lean gate was not run on this machine) nothing is dropped.
        witness = read_lean_witness()
        entry_mech = entry_mechanizations()
        lifted, mechanized, claimed = [], [], []
        for k in sorted(set(reached)):
            # per-file markers first; then the entry-level theorem docs/TRUSTED.md names
            ms = sorted(set(mech_for.get(k, ())) | set(entry_mech.get(k, ())))
            if not ms:
                continue
            claimed += [f"{k} via {m}" for m in ms]
            if all(m in witness for m in ms):
                lifted.append(k)
                mechanized += ms
        reached = sorted(set(reached) - set(lifted))
        mechanized = sorted(set(mechanized))
        rows.append(dict(name=name, verdict=verdict, negative=negative, reached=reached, gaps=sorted(set(gaps)),
                         corpus=corpus_wide, deps=len(cl), missing=sorted(missing),
                         fragile=sorted(fragile), reasserted=sorted(reasserted),
                         exists=p.is_file(), mechanized=mechanized, lifted=sorted(lifted),
                         mech_claimed=sorted(set(claimed)), orphan_mech=sorted(set(orphan_mech))))
    return rows


# TABLES WRITTEN BY A TEST SUITE, NOT BY A PROVER DRIVER.  `EquivPipelineTest` and `FixpointSemantics`
# write their tables through `ArtifactSink` and VERIFY them on every run, so a verdict this script
# rewrote would be reported as a stale artifact by the next test run.  For these, `--annotate` leaves
# the file alone and `--check` accepts a plain `PROVED` wherever the closure's own verdict is a pure
# lift (`PROVED (MECHANIZED … discharges …)` with nothing left assumed): an unqualified PROVED is
# exactly what a fully discharged closure entitles, and the emitter writes any REMAINING qualification
# itself (`Certified.qualify`, from the artifact's `; TRUSTS:` header).
TEST_OWNED = {ROOT / "proofs/pipeline/STATUS.tsv", ROOT / "proofs/pipeline/fixpoint-gate/STATUS.tsv"}


def compatible(reported, want):
    """is the reported verdict acceptable for what the closure says?"""
    if want is None or reported == want:
        return True
    return reported == "PROVED" and want.startswith("PROVED (MECHANIZED")


def want_verdict(r):
    """THE verdict a row's closure entitles it to, or None when this analysis cannot decide.

    ==ONE FUNCTION, BECAUSE TWO COPIES DISAGREED IMMEDIATELY==
    `annotate` writes a verdict and `--check` holds the table to one, and they were two expressions.
    The first version of the Lean lift had `annotate` write

        PROVED (MECHANIZED <thm> discharges T1)

    for `card_wrap` — whose closure reaches T1 AND T7 — because it branched on "was anything
    lifted?" and forgot that something else was still reached.  That is a row reported as
    UNQUALIFIED while depending on the counting axioms, i.e. exactly the defect this whole script
    exists to prevent, arriving through the mechanism meant to prevent it.  `--check` caught it on
    the next line, which is the point of having both; the fix is that there is now one function.

    The composed form keeps BOTH halves, because a reader needs both: what is still assumed, and
    what stopped being assumed and by what."""
    if not r or r["negative"]:
        return None
    # a marker row (TRIVIAL / IDENTICAL-STRUCTURE / LAW-JUSTIFIED / OPEN …) is not a prover verdict;
    # what it rests on is in its `; TRUSTS:` header and `audit_pipeline_markers.py --accept` holds it
    # to its CLAIMS.tsv row.  Only a PROVED is a claim this closure qualifies.
    if not str(r["verdict"]).startswith("PROVED"):
        return None
    reached = list(r["reached"]) + list(r.get("gaps") or [])
    mech = r.get("mechanized") or []
    lifted = r.get("lifted") or []
    if reached:
        base = "PROVED-MODULO " + ",".join(reached)
        if mech and lifted:
            return base + " (MECHANIZED " + ",".join(mech) + " discharges " + ",".join(lifted) + ")"
        return base
    if mech and lifted:
        return "PROVED (MECHANIZED " + ",".join(mech) + " discharges " + ",".join(lifted) + ")"
    return None


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
        if status in TEST_OWNED:
            print(f"left alone: {status.relative_to(ROOT)} is written by a test suite (see TEST_OWNED)")
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
            # that never needed one from a row a Lean theorem discharged.  `want_verdict` is shared
            # with `--check` so the two cannot disagree; see its docstring for the bug that caused.
            want = want_verdict(r)
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
    ap.add_argument("--inject-open", action="append", default=[],
                    help="treat this registry id as OPEN for this run (C4's mutation test: every "
                         "transitive consumer must turn conditional); implies --check")
    ap.add_argument("--expect-consumers", type=int, default=None,
                    help="with --inject-open: fail unless at least this many traces turned OPEN")
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
            if read_assert_closure() is None:
                print("  ASSERT-LEVEL CLOSURE UNAVAILABLE: target/assert-closure.tsv is absent, so this "
                      "table's SMT rows are classified only by the DECLARED entries that name them.  "
                      "Run scripts/check_asserts.py first (scripts/gates.py orders it before this).")
                if a.check:
                    problems.append(f"{status.relative_to(ROOT)}: assert-level closure table missing "
                                    "(scripts/check_asserts.py has not run), so SMT dependencies are invisible")
            else:
                print("  assert-level closure applied: every `; ASSUMED:` marker in each obligation, "
                      "transitively through its `; DERIVED-FROM:` edges (scripts/check_asserts.py, 2E.4).")
        print(f"  corpus-wide trusted entries for `{corpus}`: "
              f"{', '.join(rows[0]['corpus']) if rows else '-'}  "
              "(declared for the tier, not reachable through any include)")
        how = ("reach a trusted AXIOM through their includes" if kind == "tptp"
               else "are conditional on a DECLARED, file-scoped trusted entry")
        print(f"  {len(cond)} of {len(pos)} positive claims {how}:")
        for r in cond:
            names = ", ".join(f"{k} ({TRUSTED[k]['what']})" for k in r["reached"])
            print(f"    {r['name']:34s} {r['verdict']:12s} PROVED-MODULO {names}")
            want = want_verdict(r)
            why = ("its include closure reaches" if kind == "tptp"
                   else "a declared trusted entry names it:")
            if r["verdict"] == "PROVED":
                problems.append(f"{r['name']}: reported as unqualified PROVED, but {why} "
                                f"{', '.join(r['reached'])} -- it is CONDITIONAL. "
                                f"`--annotate` rewrites it to `{want}`.")
            elif not compatible(r["verdict"], want):
                problems.append(f"{r['name']}: reported as `{r['verdict']}` but its closure says "
                                f"`{want}`")
        # --- the Lean lifts, and the markers that could not be honoured  ------------
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
                    problems.append(f"{m}: `{thm}` is not in {status.name}, so the "
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

    check_spatial_transfers(problems)
    injected = set(a.inject_open)
    affected = check_trace_closure(problems, a.check or bool(injected), injected)
    if injected:
        n = len(affected or [])
        if a.expect_consumers is not None and n < a.expect_consumers:
            problems.append(f"injecting {sorted(injected)} as open turned only {n} consumer(s) conditional (expected >= {a.expect_consumers})")
        # an injection is a mutation test: its problems are the EXPECTED outcome, reported and then discarded
        print(f"  (injection run: {len(problems)} problem(s) reported under the mutation, exit reflects --expect-consumers only)")
        sys.exit(0 if (a.expect_consumers is None or n >= a.expect_consumers) else 1)

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
