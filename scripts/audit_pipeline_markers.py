#!/usr/bin/env python3
"""CI marker audit for the equivalence pipeline artifacts.

Classifies every file under zipper-egg-tests/pipeline/ and proofs/pipeline/ as exactly one of
  REAL            — carries actual checks/goals (egg `(check …)`; smt `(assert (not …))` goal)
  BOUNDED-UNROLLING — carries a real goal, but its sides contain a RESIDUAL CUT, so the claim is
                    about the k-unrollings at the stamped depths and quantified over the cut's free
                    input — NOT about the recursion.  Lifting it needs registry row O10b (all k plus
                    omega-continuity), which is OPEN.  Counted separately so it cannot be read as an
                    end-to-end equivalence.
  TRIVIAL         — explicit TRIVIAL-NO-OBLIGATION marker (identical sides; nothing to prove)
  IDENT           — IDENTICAL-LITERAL / IDENTICAL-STRUCTURE marker: both sides materialised to the
                    same term, so no equivalence obligation exists here; requires a REAL twin
  SINGLE-SIDE     — SINGLE-SIDE-OBSERVATION marker: the file observes ONE side against the
                    reference output; it is a real computation but NOT an equivalence
  LAW-JUSTIFIED   — proof-carrying: all differing pairs are verified certified-law instances
  BUDGET          — explicit BUDGET-EXCEEDED / PROVER-BUDGET-EXCEEDED marker (attempt log in the
                    file header; the equivalence is carried by the named certificates)
and FAILS (exit 1) on any of:
  * an unclassifiable file, or one that claims REAL with no check/goal in it;
  * a fake reflexive goal (`(assert (not true))` and friends);
  * an egg REAL file binding byte-identical large terms under two let names;
  * a VACUOUS smt goal — see `vacuous_smt`: the two sides are the same macro, byte-identical
    macro bodies, `(= X X)`, or alpha-equal after macro inlining.  THIS IS PLAN ITEM 12: the
    detector used to be gated on `if f.suffix == ".egg"`, so all 18 instance `.smt2` files —
    every one of which had two byte-identical `define-fun`s and a goal that macro-expands to
    `true` — escaped it entirely;
  * an IDENT file whose twin is missing OR is not itself REAL (a marker deferring to a marker
    certifies nothing);
An `.egg` that converged only at the TOP rounds rung (120) is REPORTED but not fatal: it used to
be the on-disk signature of "no budget succeeded" (the emitter left the last failed attempt on
disk), but the emitter now rewrites a failed ladder with an explicit BUDGET-EXCEEDED header, so a
rung-120 file today means 120 is the rung that WORKED.  `--run` settles the correctness question.
With `--run` it additionally EXECUTES the artifacts (egglog on every non-marker `.egg`, z3 on
every non-marker `.smt2`) and fails on a non-zero exit / a non-`unsat` verdict — without it "REAL"
is only a grep for `(check`, which is how six on-disk `.egg` files stayed REAL while egglog
rejected them.  The fast grep mode is the default for local use; CI should pass `--run`.
"""
import argparse, os, pathlib, re, shutil, subprocess, sys

root = pathlib.Path(__file__).resolve().parent.parent
dirs = [root / "zipper-egg-tests" / "pipeline", root / "proofs" / "pipeline"]

ap = argparse.ArgumentParser()
ap.add_argument("--run", action="store_true",
                help="actually invoke egglog/z3 on every non-marker artifact and fail on rejection")
ap.add_argument("--timeout", type=int, default=60, help="per-file prover/egglog budget in seconds")
ap.add_argument("--declare", action="store_true",
                help="rewrite proofs/pipeline/DECLARED.tsv from the OBSERVED state, then exit.  "
                     "Changing what the matrix claims should be a deliberate diff, so this is a "
                     "separate command and never happens as a side effect of an audit run.")
args = ap.parse_args()

# ==================================================================================================
# THE DECLARED MATRIX.  `proofs/pipeline/DECLARED.tsv` is the CLAIM: one row per artifact, naming
# what that cell IS.  The audit fails on any drift in either direction —
#
#   * an artifact whose observed kind differs from its declared kind.  A cell declared REAL that
#     becomes a TRIVIAL / IDENT / SINGLE-SIDE / BUDGET marker is a cell that STOPPED CARRYING AN
#     OBLIGATION, which is the regression this gate exists for; and a cell that improves fails too,
#     until the claim is updated, because the matrix is a published claim and changing a claim
#     belongs in a diff.
#   * an artifact with NO declaration — a new cell cannot arrive unclaimed;
#   * a declaration with NO artifact — the MISSING-cell case: a stone that stopped emitting a file
#     used to leave no trace at all, since the audit only ever walked what was on disk.
#
# This is the honest half of the acceptance review's item 3: the pipeline matrix is NOT a
# full-support table, and rather than let a reader infer its shape from marker vocabulary the shape
# is written down and checked.  Discharging the cells is the other half and is open — see
# plan.md, Track A′ (item 4).
DECLARED_FILE = root / "proofs" / "pipeline" / "DECLARED.tsv"


def read_declared():
    """-> {artifact -> declared kind}, or None when the file is absent."""
    if not DECLARED_FILE.exists():
        return None
    out = {}
    for line in DECLARED_FILE.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) >= 2:
            out[parts[0]] = parts[1]
    return out


def write_declared(observed):
    """The claim, regenerated from the observed state.  Sorted, so a diff is readable."""
    body = ["# THE DECLARED PIPELINE MATRIX — what each emitted artifact IS.",
            "#",
            "# Regenerate with `python3 scripts/audit_pipeline_markers.py --declare`, and READ THE DIFF:",
            "# every line that changes is a change to what this tree claims about that cell.",
            "# `scripts/audit_pipeline_markers.py` fails on any artifact whose observed kind differs",
            "# from its declaration, on an artifact with no declaration, and on a declaration whose",
            "# artifact is MISSING.",
            "#",
            "# The kinds, and what each is worth:",
            "#   REAL           a prover/egglog obligation with actual checks or a real goal.  The only",
            "#                  kind that is a certified equivalence for that cell.",
            "#   TRIVIAL        the two sides are the same term after alpha-normalisation; there is NO",
            "#                  obligation to discharge.",
            "#   IDENT          both sides materialised to byte-equal terms (IDENTICAL-LITERAL /",
            "#                  IDENTICAL-STRUCTURE); no equivalence obligation exists here either.",
            "#   SINGLE-SIDE    ONE side observed against the reference output.  A real computation,",
            "#                  NOT an equivalence.",
            "#   LAW-JUSTIFIED  every differing pair replayed as an instance of a certified law, so the",
            "#                  universal certificates in proofs/ are the proof; not proved per program.",
            "#   BUDGET         neither prover / no rounds rung reached it; the attempt log is in the",
            "#                  file header.  An OPEN obligation, not an acceptance.",
            "#",
            "# artifact\tdeclared-kind"]
    body += [f"{k}\t{v}" for k, v in sorted(observed.items())]
    DECLARED_FILE.write_text("\n".join(body) + "\n")

counts = {"REAL": 0, "TRIVIAL": 0, "LAW-JUSTIFIED": 0, "BUDGET": 0, "IDENT": 0, "SINGLE-SIDE": 0,
          "BOUNDED-UNROLLING": 0}
problems = []
expected_open = []
costly = []
seen_open = set()
rows = []

FAKE_GOALS = ["(assert (not true))", "(assert (not (and)))", "(assert (not (and )))", "(assert false)"]
TOP_RUNG = 120                      # the last rung of EquivPipelineTest.runEggFileOpt's ladder

# RECORDED GAP, with a RATCHET rather than a name list (names move between runs as a stone's egg
# ladder converges or does not, and a name list would fail CI on jitter).  An IDENT cell whose twin
# is ALSO a marker certifies nothing: the equivalence content has nowhere to live.  The cause is
# plan item 3 STEP 3 — `EquivPipeline.expand` evaluates control flow on BOTH sides, so
# `formalOf(eO) == formalOf(eP)` and the stage-1/stage-2 instance legs are literal-vs-literal; the
# fix is to render them WITHOUT evaluating Iteration/Fixpoint (the `-virtual` Iter/BodyK form).
# Until then every such chain is printed as EXPECTED-OPEN and the COUNT is pinned: it may shrink,
# never grow.  MEASURED 2026-08-31 over the seven stones: 12 (nine `-graph`/`-space` cells whose
# agnostic twin is TRIVIAL, plus temperature-zipper and two egg twins).
MAX_MARKER_CHAINS = 12


def duplicate_big_lets(text):
    """Two DIFFERENT let names bound to byte-identical large RHS text: the signature of a vacuous
    'equivalence' between hash-cons-equal constructor terms (e.g. a pre-materialised zipper side
    vs the reference literal).  Such files must carry the IDENTICAL-LITERAL marker instead."""
    seen = {}
    for m in re.finditer(r"^\(let (\$\w+) (.+)\)\s*$", text, re.M):
        name, rhs = m.group(1), m.group(2)
        if len(rhs) < 80:
            continue
        if rhs in seen and seen[rhs] != name:
            return (seen[rhs], name)
        seen[rhs] = name
    return None


def smt_defs(text):
    """non-recursive (define-fun n ((p Path)) Bool BODY) macros, in emission order."""
    return re.findall(r"^\(define-fun (\w+) \(\((\w+) Path\)\) Bool (.*)\)$", text, re.M)


_BV = re.compile(r"\b(?:[qhgw]|s|m|in|bv|bm|rng|fix|tails)_\d+\b")


def alpha_norm(term, defs, depth_cap=64):
    """Macro-inline every define-fun, then canonically renumber the generated names.  The macros
    Smt.den/AgSmt.den emit are non-recursive, single-argument and never shadow, so the inlining
    terminates; `depth_cap` guards against a hand-edited file and makes the caller treat a
    non-terminating inline as INCONCLUSIVE rather than clean."""
    bodies = {n: b for n, _p, b in defs}
    prev, steps = None, 0
    while prev != term and steps < depth_cap:
        prev, steps = term, steps + 1
        def sub(m):
            b = bodies.get(m.group(1))
            return m.group(0) if b is None else "(" + b.replace("p", m.group(2)) + ")"
        term = re.sub(r"\((\w+) ([^()]*|\([^()]*\))\)", sub, term)
    if steps >= depth_cap:
        return None                                   # inconclusive
    seen, out, i = {}, [], 0
    for tok in re.split(r"(\W)", term):
        if _BV.fullmatch(tok):
            if tok not in seen:
                i += 1
                seen[tok] = f"v{i}"
            out.append(seen[tok])
        else:
            out.append(tok)
    return "".join(out)


def vacuous_smt(text):
    """Return a reason string if the goal is vacuous, else None.  Four patterns:
       (1) same macro — the two sides of the goal are the SAME symbol (the shared-subterm encoder
           gives structurally identical sides one name, so this is the exact test);
       (2) macro     — two define-fun macros with byte-identical bodies used as the two sides;
       (3) X X       — a goal conjunct of the form (= X X);
       (4) alpha     — the two sides differ only in generated-name numbering after inlining."""
    defs = smt_defs(text)
    bodies = {}
    for n, _p, b in defs:
        if len(b) < 40:
            continue
        if b in bodies:
            return f"macros {bodies[b]} and {n} have byte-identical bodies"          # (2)
        bodies[b] = n
    for goal in re.findall(r"\(assert \(not (.*)\)\)\s*$", text, re.M | re.S):
        for l, r in re.findall(r"\(= (\(.*?\)) (\(.*?\))\)", goal):
            if l == r:
                return f"goal conjunct is (= X X): {l[:60]}"                          # (3)
            ln, rn = alpha_norm(l, defs), alpha_norm(r, defs)
            if ln is not None and ln == rn:
                return f"goal sides are alpha-equal after macro inlining: {l[:60]}"   # (4)
        # (1) the ∀ form: (forall ((p Path)) (= (m_i p) (m_j p))) with i == j
        for a, b in re.findall(r"\(= \((\w+) (?:\w+)\) \((\w+) (?:\w+)\)\)", goal):
            if a == b:
                return f"both goal sides are the SAME macro {a}"
    return None


def top_rung(text):
    """an .egg emitted at the TOP rounds rung — i.e. every cheaper budget had already failed."""
    for m in re.finditer(r"\((?:run|repeat) (\d+)", text):
        if int(m.group(1)) == TOP_RUNG:
            return True
    return False


def tool(name, env_var):
    return os.environ.get(env_var) or shutil.which(name)


def run_artifact(f, kind):
    """--run: execute the artifact and return an error string, or None."""
    if kind != "REAL":
        return None
    if f.suffix == ".egg":
        egglog = tool("egglog", "EGGLOG")
        if egglog is None:
            return "egglog not found (set $EGGLOG or put it on PATH) — cannot honour --run"
        cmd = f"ulimit -v 4000000; exec '{egglog}' 'pipeline/{f.name}'"
        p = subprocess.run(["/bin/sh", "-c", cmd], cwd=f.parent.parent,
                           capture_output=True, text=True, timeout=args.timeout + 15)
        if p.returncode != 0:
            tail = (p.stdout + p.stderr).strip().splitlines()[-2:]
            return f"egglog REJECTED it (exit {p.returncode}): {' | '.join(tail)}"
        return None
    z3 = tool("z3", "Z3")
    if z3 is None:
        return "z3 not found (set $Z3 or put it on PATH) — cannot honour --run"
    p = subprocess.run([z3, f"-T:{args.timeout}", str(f)], capture_output=True, text=True,
                       timeout=args.timeout + 15)
    last = (p.stdout + p.stderr).strip().splitlines()
    verdict = last[-1].strip() if last else "(no output)"
    if verdict == "sat":
        return "z3 answered SAT — the stated equivalence is FALSE (countermodel)"
    if verdict != "unsat":
        return (f"z3 did not discharge it ({verdict}) — a REAL cell must be provable or carry a "
                "PROVER-BUDGET-EXCEEDED marker with its attempt log")
    return None


for d in dirs:
    for f in sorted(d.glob("*")):
        if f.suffix not in (".egg", ".smt2"):
            continue
        text = f.read_text()
        for fake in FAKE_GOALS:
            if fake in text:
                problems.append(f"{f.relative_to(root)}: FAKE reflexive goal `{fake}`")
        if "TRIVIAL-NO-OBLIGATION" in text:
            kind = "TRIVIAL"
        elif "SINGLE-SIDE-OBSERVATION" in text:
            # ONE side observed against the reference output.  A real computation in the certified
            # system, but not an equivalence: it must never be counted REAL (five `-lit` fallback
            # files were, and they only proved that the reference literal observes itself).
            kind = "SINGLE-SIDE"
        elif ("IDENTICAL-LITERAL-NO-EQUIVALENCE-OBLIGATION" in text
              or "IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION" in text):
            kind = "IDENT"
            # the equivalence content must live somewhere, and that twin must itself be REAL —
            # `twin.exists()` alone let markers defer to markers.
            # an .egg `-zipper` cell defers to the VIRTUAL (Iter/BodyK, un-materialised) twin, which
            # exists only in the egg vocabulary; every other IDENT cell defers to its data-agnostic
            # twin (the ∀-inputs comparison of the same stage).
            twin = None
            zipper_rep = "-zipper-virtual.egg" if f.suffix == ".egg" else "-zipper-agnostic.smt2"
            for suf, rep in ((f"-zipper{f.suffix}", zipper_rep),
                             (f"-space{f.suffix}", f"-space-agnostic{f.suffix}"),
                             (f"-graph{f.suffix}", f"-graph-agnostic{f.suffix}")):
                if f.name.endswith(suf):
                    twin = f.with_name(f.name.replace(suf, rep))
                    break
            if twin is not None:
                if not twin.exists():
                    problems.append(f"{f.relative_to(root)}: IDENTICAL marker but no {twin.name} "
                                    "twin carrying the actual equivalence certificate")
                else:
                    tt = twin.read_text()
                    if any(k in tt for k in ("TRIVIAL-NO-OBLIGATION", "BUDGET-EXCEEDED",
                                             "SINGLE-SIDE-OBSERVATION",
                                             "IDENTICAL-LITERAL-NO-EQUIVALENCE-OBLIGATION",
                                             "IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION")):
                        rel = str(f.relative_to(root))
                        msg = (f"{rel}: IDENTICAL marker defers to {twin.name}, which is itself a "
                               "MARKER — no cell in this chain carries an equivalence obligation")
                        expected_open.append(msg)
                        seen_open.add(rel)
        elif "LAW-JUSTIFIED" in text and "BUDGET-EXCEEDED" not in text and (
                "LAW-JUSTIFIED-NO-RESIDUAL" in text or "LAW-JUSTIFIED:" in text):
            kind = "LAW-JUSTIFIED"
        elif "BUDGET-EXCEEDED" in text:
            kind = "BUDGET"
        else:
            # A REAL GOAL WHOSE SIDES CARRY A RESIDUAL CUT IS NOT AN END-TO-END EQUIVALENCE.  The
            # stamp is written by EquivPipelineTest.agnosticLegs from `AgnosticPipeline.residualsOf`;
            # counting it apart from REAL is what stops registry row O10b's open antecedent being
            # read as a discharged one.
            kind = "BOUNDED-UNROLLING" if "BOUNDED-UNROLLING (k=" in text else "REAL"
            has_goal = ("(check" in text) if f.suffix == ".egg" else bool(
                re.search(r"\(assert \(not ", text))
            if not has_goal:
                problems.append(f"{f.relative_to(root)}: claims {kind} but contains no check/goal")
            if f.suffix == ".egg":
                dup = duplicate_big_lets(text)
                if dup:
                    problems.append(f"{f.relative_to(root)}: lets {dup[0]} and {dup[1]} bind "
                                    "byte-identical large terms — a vacuous hash-consing "
                                    "'equivalence'; needs the IDENTICAL-LITERAL marker or a real "
                                    "structural side")
            else:
                why = vacuous_smt(text)
                if why:
                    problems.append(f"{f.relative_to(root)}: VACUOUS obligation — {why}; emit the "
                                    "un-folded structural sides or carry an honest marker")
        if f.suffix == ".egg" and kind in ("REAL", "IDENT", "SINGLE-SIDE") and top_rung(text):
            # A rung-120 file USED to be the on-disk signature of "no budget succeeded", because
            # `runEggFileOpt` wrote the file before each attempt and left the last, failed one
            # there.  The emitter no longer does that — a failed ladder is now rewritten with an
            # explicit BUDGET-EXCEEDED header and its attempt log — so the syntactic rule has
            # flipped meaning: a rung-120 file today is one where 120 is the rung that WORKED.
            # Failing on it would be a false positive, so this is now a COST signal, reported and
            # not fatal; the correctness question is settled by `--run`, which executes the file.
            #
            # THE MEASUREMENT THAT USED TO BE QUOTED HERE NAMED A FILE THAT NO LONGER EXISTS.  It
            # cited a `-space-lit` fallback sitting at rung 120 and being accepted — but that file
            # was a BUDGET marker whose attempt log read `Unbound function SelfBody`, i.e. it
            # existed only because `bridge-prelude.egg` did not load at all.  With that fixed the
            # `-impl` fallback works, the `-lit` degradation is never reached, and the file is gone.
            # MEASURED 2026-09-02 with all three tools present: `--run` accepts every non-marker
            # artifact in both directories, which is the check that comment was standing in for.
            costly.append(f"{f.relative_to(root)}: converged only at the TOP rounds rung "
                          f"({TOP_RUNG}) — the most expensive cell in the ladder")
        if args.run:
            err = run_artifact(f, kind)
            if err:
                problems.append(f"{f.relative_to(root)}: {err}")
        counts[kind] += 1
        rows.append((str(f.relative_to(root)), kind))

width = max((len(r[0]) for r in rows), default=0)
for path, kind in rows:
    print(f"{path:<{width}}  {kind}")
print()
print("  ".join(f"{k}={v}" for k, v in counts.items()), f" total={sum(counts.values())}")
print(f"mode: {'--run (artifacts executed)' if args.run else 'grep-only (pass --run in CI)'}")

if costly:
    print(f"\nTOP-RUNG ({len(costly)} cell(s) that converge only at rounds {TOP_RUNG}):")
    for c in costly:
        print(f"  {c}")
if expected_open:
    print(f"\nEXPECTED-OPEN ({len(expected_open)} marker-to-marker chain(s), ratchet {MAX_MARKER_CHAINS} "
          "— plan item 3 STEP 3):")
    for e in expected_open:
        print(f"  {e}")
# ---- the declared matrix ------------------------------------------------------------------------
observed = dict(rows)
if args.declare:
    write_declared(observed)
    print(f"\nwrote {DECLARED_FILE.relative_to(root)} with {len(observed)} declarations — READ THE DIFF")
    sys.exit(0)

declared = read_declared()
if declared is None:
    problems.append(f"{DECLARED_FILE.relative_to(root)} is missing — the pipeline matrix has no "
                    "declared shape, so nothing can detect a cell that stops carrying an obligation. "
                    "Create it with `--declare`.")
else:
    drift = sorted((a, declared[a], observed[a]) for a in observed.keys() & declared.keys()
                   if declared[a] != observed[a])
    undeclared = sorted(observed.keys() - declared.keys())
    missing = sorted(declared.keys() - observed.keys())
    if drift:
        print(f"\nDRIFT ({len(drift)} cell(s) whose kind changed):")
        for a, d, o in drift:
            print(f"  {a}: declared {d}, observed {o}")
    for a, d, o in drift:
        problems.append(f"{a}: declared {d} but is {o}. " +
                        ("A cell that STOPPED carrying an obligation." if d == "REAL" else
                         "Update DECLARED.tsv with `--declare` and put the change in the diff."))
    for a in undeclared:
        problems.append(f"{a}: emitted but NOT DECLARED — a new cell may not arrive unclaimed "
                        f"(observed {observed[a]}); run `--declare`")
    for a in missing:
        problems.append(f"{a}: DECLARED {declared[a]} but NOT EMITTED — the missing-cell case; the "
                        "stone stopped producing this artifact")
    print(f"\ndeclared matrix: {len(declared)} cell(s), {len(drift)} drifted, "
          f"{len(undeclared)} undeclared, {len(missing)} missing")
    kinds = {}
    for k in declared.values():
        kinds[k] = kinds.get(k, 0) + 1
    print("  declared kinds: " + "  ".join(f"{k}={v}" for k, v in sorted(kinds.items())) +
          f"   (REAL is the only kind that is a certified equivalence: "
          f"{kinds.get('REAL', 0)}/{len(declared)})")

if len(expected_open) > MAX_MARKER_CHAINS:
    problems.append(f"{len(expected_open)} marker-to-marker chains, above the pinned ratchet of "
                    f"{MAX_MARKER_CHAINS} — a cell that used to carry an obligation stopped carrying "
                    "one; lower the ratchet only when the count actually drops")

if problems:
    print("\nPROBLEMS:")
    for p in problems:
        print(f"  {p}")
    sys.exit(1)
print("\nmarker audit: OK")
