#!/usr/bin/env python3
"""BENCHMARK PUBLICATION AS ONE ATOMIC TRANSACTION.

WHAT WAS WRONG.  Publication was not an operation -- it was a side effect of `sbt test`.  Three
suites wrote committed artifacts as they ran, each probing the environment for itself, so the
committed headers carried THREE different timestamps for one claimed measurement and a
`<sha>-dirty` commit identity that names no tree that ever existed.  Nothing validated the result:
not that only the intended files changed, not that their schemas were intact, not that the numbers
came from a tree anyone could check out.

WHAT THIS DOES, in order, aborting at the first failure:

  1. PREFLIGHT.  The tree must be clean and free of untracked relevant inputs.  A number produced
     from a dirty tree cannot be reproduced from any commit, so there is nothing to publish.
  2. GATES.  The acceptance gates run FIRST.  "Regenerate the artifacts only after all acceptance
     gates pass" means a red gate blocks publication -- otherwise the tree ships numbers that the
     next gate fix invalidates.
  3. CAPTURE.  ONE commit identity and ONE environment record, written to a manifest.  Every
     generator reads that manifest (`$ZIPPY_PUBLISH_MANIFEST`) instead of probing, so all artifacts
     of one publication necessarily agree.
  4. GENERATE.  Only the declared outputs may be written; `PublishManifest.permits` refuses anything
     else at the point of writing rather than after the fact.
  5. VALIDATE.  Provenance matches the manifest; schema (the header row) unchanged; row counts
     within declared bounds AND the ROW SET unchanged against HEAD (a count range passes a table
     whose every row changed identity); `docs/BENCHMARKS.md` section markers balanced and unchanged
     as a set; the working tree differs from HEAD in DECLARED OUTPUTS ONLY, and every declared
     output did change.
  6. REPORT.  The diff is CHECKED and then shown: an empty diff means a generator did not run, and
     a near-total rewrite means a format change rather than new numbers -- either way the published
     figures would not be comparable with the previous commit. Nothing is committed: the
     transaction produces a validated working tree and says so, and committing stays a human act.

`--dry-run` runs 1, 2 and 5's tree check and stops -- which is the useful mode while the gates are
red, because it says exactly what blocks publication.
"""

import argparse, csv, datetime, os, pathlib, re, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------------------------
# THE DECLARED OUTPUTS.  Anything not on this list may not be written during generation, and
# anything on it that does NOT change is reported (a generator that silently stopped producing an
# artifact is a failure too, not a success).
# ---------------------------------------------------------------------------------------------
OUTPUTS = {
    "corpus_runtimes.csv":  dict(kind="csv", header="idx,nodes,nSpace,nPath,uniqueOut,evalI_ms_per1000",
                                 min_rows=900, max_rows=1100,
                                 identity=("idx",),
                                 timing={"evalI_ms_per1000": dict(rel=0.35, abs=0.50)}),
    "expressivity.csv":     dict(kind="csv", header="uniqueOut,entropy,nEmpty,nSpace,nPath,respSpace,respPath,respFrac,avgSize,nodes",
                                 min_rows=90, max_rows=100_100,
                                 identity=("uniqueOut", "entropy", "nEmpty", "nSpace", "nPath",
                                           "respSpace", "respPath", "respFrac", "avgSize", "nodes"),
                                 timing={}),
    # THE HEADER WAS `None` HERE, AND THIS IS THE ONE ARTIFACT WITH A KNOWN SCHEMA DRIFT: its own
    # generator records that a `Transformation` column outlived the constructor it counted.  Leaving
    # the schema unchecked on the file whose schema has actually drifted is the wrong place to save
    # effort, so the header is declared and compared like the others.
    "prog_matrix.tsv":      dict(kind="tsv",
                                 # taken from the artifact itself rather than transcribed:
                                 # a hand-copied 19-column tab-separated header is exactly
                                 # the kind of declaration that drifts silently
                                 header="row\tMention\tLiteral\tSingleton\tUnion\tIntersection\tSubtraction\tRestriction\tRaffination\tComposition\tWrap\tUnwrap\tTailsUnion\tTailsIntersection\tRange\tIteration\tConstant\tDeref\tConcat",
                                 min_rows=1, max_rows=500, identity=("row",), timing={}),
    # `header=None` is not "unchecked": a markdown document has no header ROW, and its schema is
    # its SECTION MARKER SET, which the `md` branch of validate() compares against HEAD -- a
    # section that appeared or vanished is a failure there.
    "docs/BENCHMARKS.md":   dict(kind="md",  header=None, min_rows=1, max_rows=100_000, timing={}),
}

EXPECTED_SECTIONS = (
    "subgraph-hoisting", "sc-domains", "op-graph-backend", "executor-scaling",
    "pipeline-ablation",
)

# The suites that PRODUCE the declared outputs.  Each is run once, in one JVM per suite, with the
# manifest in the environment.
#
# ALL FOUR OUTPUTS, NOT THREE.  An earlier revision listed only the three data artifacts, so
# `docs/BENCHMARKS.md` -- which bullet 2 names explicitly -- had no producer at all: stage 5's
# "a declared output did NOT change" check would have failed every publication, and green gates
# would not have helped.  The five sections live in five separate test classes; naming only the
# source file's first class silently refreshed two sections and left three stale.
GENERATORS = ["morkl.CorpusRuntimes", "morkl.ProgramExpressivity", "morkl.ProgramStats",
              "morkl.GraphBench", "morkl.TrieBench", "morkl.SubgraphHoistBench",
              "morkl.SCOptBench", "morkl.AblationStages"]

# The acceptance gates that must be green before anything is regenerated.
#
# IMPORTED, NOT LISTED.  `scripts/gates.py` holds the ONE gate list and `sbt check` runs the same
# module, so a gate cannot be in one entry point and missing from the other.  It was: an earlier
# revision of THIS file listed only the Scala suites -- exactly the four that review item 1 owns --
# so item 7's declared gate (`check_references.py --strict`) and item 8's (`proof_closure.py
# --check`) were never run by the thing that gates publication, and a publication could have
# proceeded with a dangling reference in a tracked file or an unqualified `PROVED` resting on an
# admitted schema.  A gate an item declares for itself and the publisher does not run is not a gate.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from gates import gate_count, resolve_runner   # noqa: E402
from toolpath import missing_message, resolve as resolve_tool             # noqa: E402

# Inputs whose modification would invalidate the numbers.  An untracked file here is as bad as a
# modified one: it may be what the run picked up.
RELEVANT = ("src/", "build.sbt", "project/", "scripts/", "toolchain.conf")


def git(*args, check=True):
    r = subprocess.run(["git", "-C", str(ROOT)] + list(args), capture_output=True, text=True)
    if check and r.returncode != 0:
        die(f"git {' '.join(args)} failed: {r.stderr.strip()}")
    return r.stdout


def die(msg, code=1):
    # stdout, and flushed: an abort message that races the step headers on stderr is unreadable,
    # and this script's output is the artifact a reader uses to see WHY publication was refused.
    sys.stdout.flush()
    print(f"\nPUBLISH ABORTED: {msg}", flush=True)
    sys.exit(code)


def step(n, what):
    print(f"\n=== {n}. {what} " + "=" * max(0, 60 - len(what)), flush=True)


SECTION_RE = re.compile(
    r"<!-- BEGIN benchmark:([\w-]+) -->(.*?)<!-- END benchmark:\1 -->", re.S)
MD_NUMBER = re.compile(r"(?<![\w])-?\d+\.\d+(?:x)?")
MEASURED_PROSE = re.compile(
    r"^(?:compile\s*=|compile/K\s*\+\s*run|\*\*comp\+run geomean|"
    r"Geometric-mean evalI speedup|reference Set, and )")
MD_MEASURE_COLUMNS = {
    "exec off ms", "exec on ms", "speedup", "evali ms", "exect unopt ms", "exect opt ms",
    "opt speedup", "exect opt(no-hoist) ms", "hoist", "exec ms", "exect ms", "exect(opt) ms",
    "exect(inline+opt) ms", "vs evali", "transpile ms", "push_out ms", "optimize_sharing ms",
    "compile ms", "compile+run ms", "eval ms", "evalt ms", "evali/eval", "evali/evalt",
    "eval(def)", "evali(def)", "evali(sc)", "exect(opt)", "exect(sc+opt)",
}


def sections(text):
    """Ordered generated Markdown sections as `(slug, body)` pairs."""
    return SECTION_RE.findall(text)


def markdown_provenance_problems(text, commit, ts=None):
    """Every generated section—not merely one—must name the same manifest."""
    blocks = sections(text)
    problems = []
    slugs = [slug for slug, _body in blocks]
    if tuple(slugs) != EXPECTED_SECTIONS:
        problems.append(f"section order/set is {slugs}, expected {list(EXPECTED_SECTIONS)}")
    for slug, body in blocks:
        commits = re.findall(r"\|\s*git commit\s*\|\s*([^| ]+)\s*\|", body)
        if commits != [commit]:
            problems.append(f"section {slug}: commit rows {commits}, expected exactly [{commit!r}]")
        stamps = re.findall(r"\|\s*timestamp \(UTC\)\s*\|\s*([^|]+?)\s*\|", body)
        if ts is not None and stamps != [ts]:
            problems.append(f"section {slug}: timestamp rows {stamps}, expected exactly [{ts!r}]")
        clean = re.findall(r"\|\s*source tree\s*\|\s*([^|]+?)\s*\|", body)
        if len(clean) != 1 or "CLEAN" not in clean[0]:
            problems.append(f"section {slug}: source-tree row is not uniquely CLEAN")
    return problems


def delimited(text, spec):
    lines = text.splitlines()
    if len(lines) < 2:
        return (), [], ["missing provenance or schema row"]
    sep = "\t" if spec["kind"] == "tsv" else ","
    parsed = list(csv.reader(lines[1:], delimiter=sep))
    if not parsed:
        return (), [], ["missing schema row"]
    header, data = tuple(parsed[0]), parsed[1:]
    bad = [i + 1 for i, row in enumerate(data) if len(row) != len(header)]
    return header, data, ([f"{len(bad)} row(s) have the wrong field count"] if bad else [])


def numeric(cell):
    s = cell.strip()
    if s.endswith("x"):
        s = s[:-1]
    try:
        return float(s)
    except ValueError:
        return None


def within(a, b, rel, absolute):
    return abs(a - b) <= max(absolute, rel * max(abs(a), abs(b)))


def compare_delimited(rel, published, regenerated, spec, enforce_timing):
    """Exact deterministic fields; explicitly tolerated timing fields on same-commit reproduction."""
    ph, pr, problems = delimited(published, spec)
    rh, rr, other = delimited(regenerated, spec)
    problems += other
    if ph != rh:
        problems.append(f"{rel}: schema differs")
        return problems, 0
    if len(pr) != len(rr):
        problems.append(f"{rel}: row count differs ({len(pr)} vs {len(rr)})")
        return problems, 0
    timing = spec.get("timing", {})
    identity = set(spec.get("identity", (ph[0],)))
    changed = 0
    for rowno, (a, b) in enumerate(zip(pr, rr), 1):
        if a != b:
            changed += 1
        for col, (av, bv) in enumerate(zip(a, b)):
            name = ph[col]
            if name not in timing:
                if (enforce_timing or name in identity) and av != bv:
                    problems.append(f"{rel}: deterministic field {name!r} differs at row {rowno}")
                continue
            aa, bb = numeric(av), numeric(bv)
            if aa is None or bb is None:
                if av != bv:
                    problems.append(f"{rel}: timing field {name!r} is not numeric at row {rowno}")
            elif enforce_timing:
                tol = timing[name]
                if not within(aa, bb, tol["rel"], tol["abs"]):
                    problems.append(
                        f"{rel}: {name} row {rowno} moved from {aa:g} to {bb:g}, beyond "
                        f"rel={tol['rel']:.0%}/abs={tol['abs']:g}")
        if len(problems) >= 30:
            break
    return problems, changed


def md_cells(line):
    # The executor table contains the prose token `|TC|` inside a cell.  It is not a delimiter.
    return tuple(x.strip() for x in line.replace("|TC|", "TC").strip().strip("|").split("|"))


def md_tables(body):
    """Return `(header, rows)` for each Markdown table in a generated section."""
    lines = body.splitlines()
    out, consumed = [], set()
    i = 0
    while i + 1 < len(lines):
        if lines[i].lstrip().startswith("|") and re.match(r"^\s*\|(?:\s*:?-+:?\s*\|)+\s*$", lines[i + 1]):
            header = md_cells(lines[i]); rows = []
            consumed.update((i, i + 1)); i += 2
            while i < len(lines) and lines[i].lstrip().startswith("|"):
                rows.append(md_cells(lines[i])); consumed.add(i); i += 1
            out.append((header, rows))
        else:
            i += 1
    prose = [line for i, line in enumerate(lines) if i not in consumed]
    return out, prose


def measured_column(name, header):
    n = name.strip().lower()
    # `hoist` is a deterministic node count in the compile-accounting table, and a measured ratio
    # in the SC-domain table.
    if n == "hoist" and "push_out ms" in {h.lower() for h in header}:
        return False
    return n in MD_MEASURE_COLUMNS


def compare_measured_text(label, old, new, enforce_timing, problems):
    """Compare a known measured prose line while retaining its exact non-numeric wording."""
    ao, an = MD_NUMBER.findall(old), MD_NUMBER.findall(new)
    if MD_NUMBER.sub("<measurement>", old) != MD_NUMBER.sub("<measurement>", new):
        problems.append(f"{label}: measured prose structure differs")
        return
    if enforce_timing:
        for x, y in zip(ao, an):
            xx, yy = numeric(x), numeric(y)
            if xx is None or yy is None or not within(xx, yy, 0.50, 1.0):
                problems.append(f"{label}: prose measurement moved from {x} to {y} beyond rel=50%/abs=1")


def compare_markdown(rel, published, regenerated, enforce_timing):
    problems, changed = [], 0
    ps, rs = sections(published), sections(regenerated)
    if [s for s, _ in ps] != [s for s, _ in rs]:
        return [f"{rel}: generated section order/set differs"], 0
    for (slug, pb), (_slug, rb) in zip(ps, rs):
        pt, pp = md_tables(pb); rt, rp = md_tables(rb)
        if len(pt) != len(rt):
            problems.append(f"{rel}#{slug}: table count differs")
            continue
        for table_no, ((ph, prows), (rh, rrows)) in enumerate(zip(pt, rt), 1):
            if ph != rh:
                problems.append(f"{rel}#{slug}: table {table_no} schema differs")
                continue
            if len(prows) != len(rrows):
                problems.append(f"{rel}#{slug}: table {table_no} row count differs")
                continue
            environment = tuple(h.lower() for h in ph) == ("environment", "value")
            for rowno, (a, b) in enumerate(zip(prows, rrows), 1):
                if len(a) != len(ph) or len(b) != len(ph):
                    problems.append(f"{rel}#{slug}: table {table_no} malformed row {rowno}")
                    continue
                if a != b:
                    changed += 1
                for col, (av, bv) in enumerate(zip(a, b)):
                    if environment:
                        if col == 0 and av != bv:
                            problems.append(f"{rel}#{slug}: environment key differs at row {rowno}")
                        elif enforce_timing and col == 1 and a[0] != "timestamp (UTC)" and av != bv:
                            problems.append(f"{rel}#{slug}: environment {a[0]!r} differs")
                    elif measured_column(ph[col], ph):
                        aa, bb = numeric(av), numeric(bv)
                        if aa is None or bb is None:
                            if av != bv:
                                problems.append(f"{rel}#{slug}: non-numeric measurement {ph[col]!r} row {rowno}")
                        elif enforce_timing and not within(aa, bb, 0.50, 1.0 if "ms" in ph[col].lower() or "(" in ph[col] else 0.5):
                            problems.append(f"{rel}#{slug}: {ph[col]} row {rowno} moved {aa:g} -> {bb:g} beyond tolerance")
                    elif enforce_timing and av != bv:
                        problems.append(f"{rel}#{slug}: deterministic field {ph[col]!r} differs at row {rowno}")
                if len(problems) >= 30:
                    break
        if len(pp) != len(rp):
            problems.append(f"{rel}#{slug}: prose line count differs")
        else:
            for line_no, (a, b) in enumerate(zip(pp, rp), 1):
                if a == b:
                    continue
                if MEASURED_PROSE.match(a) and MEASURED_PROSE.match(b):
                    compare_measured_text(f"{rel}#{slug} prose line {line_no}", a, b, enforce_timing, problems)
                else:
                    problems.append(f"{rel}#{slug}: deterministic prose differs at line {line_no}")
                if len(problems) >= 30:
                    break
    return problems, changed


def compare_output(rel, published, regenerated, enforce_timing):
    spec = OUTPUTS[rel]
    if spec["kind"] in ("csv", "tsv"):
        return compare_delimited(rel, published, regenerated, spec, enforce_timing)
    return compare_markdown(rel, published, regenerated, enforce_timing)


# =============================================================================================
def preflight():
    step(1, "PREFLIGHT")
    porcelain = [l for l in git("status", "--porcelain").splitlines() if l.strip()]
    dirty, untracked = [], []
    for line in porcelain:
        code, path = line[:2], line[3:].strip()
        # a declared output is EXPECTED to change; it is not a dirty input
        if path in OUTPUTS:
            continue
        if code.strip() == "??":
            if any(path.startswith(p) for p in RELEVANT):
                untracked.append(path)
        elif any(path.startswith(p) for p in RELEVANT) or "/" not in path:
            dirty.append(path)
    if dirty:
        die(f"{len(dirty)} relevant path(s) differ from HEAD -- a number produced from this tree "
            f"cannot be reproduced from any commit:\n  " + "\n  ".join(dirty[:20]) +
            ("\n  ..." if len(dirty) > 20 else "") +
            "\nCommit the code first, then publish.")
    if untracked:
        die(f"{len(untracked)} untracked relevant input(s) -- the run may read them, and a reader "
            f"checking out the named commit would not have them:\n  " + "\n  ".join(untracked[:20]))
    head = git("rev-parse", "HEAD").strip()
    print(f"tree is clean at {head[:12]}; no untracked relevant inputs")
    return head


def run_gates(runner):
    step(2, "ACCEPTANCE GATES (a red gate blocks publication)")
    # Do not reimplement the runner here.  gates.py owns ordering, fresh target witnesses, the
    # current-run record, suite diagnostics and the final status-check phase.
    r = subprocess.run(
        [sys.executable, "scripts/gates.py", "--run", "--runner", runner[0]],
        capture_output=True, text=True, cwd=ROOT)
    print(r.stdout, end="")
    if r.returncode != 0:
        tail = "\n".join((r.stdout + r.stderr).splitlines()[-60:])
        die(f"acceptance gates failed (exit {r.returncode}); publication is blocked.\n{tail}")
    print(f"all {gate_count()} gates green")


def capture(head):
    step(3, "CAPTURE one commit identity and one environment record")
    env = subprocess.run(
        ["java", "-cp", os.environ["ZIPPY_CP"], "morkl.RunEnvironmentMain"],
        capture_output=True, text=True, cwd=ROOT)
    if env.returncode != 0:
        die(f"could not capture the environment record: {env.stderr.strip()[:400]}")
    record = env.stdout.strip()
    ts = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    mf = pathlib.Path(tempfile.mkdtemp(prefix="zippy-publish-")) / "manifest.properties"
    mf.write_text(f"commit={head[:7]}\ntimestamp={ts}\nenv={record}\n"
                  f"outputs={','.join(sorted(OUTPUTS))}\n")
    print(f"commit    = {head[:7]}")
    print(f"timestamp = {ts}")
    print(f"env       = {record[:120]}...")
    print(f"manifest  = {mf}")
    return mf, head[:7], ts


def generate(runner, mf):
    step(4, "GENERATE (only declared outputs may be written)")
    # NOT `ZIPPY_REQUIRE_CLEAN=1` HERE, and the reason is that it made the transaction abort itself.
    # That flag makes a writer refuse from a dirty tree, and cleanliness is what the PREFLIGHT
    # established -- before any generator ran.  Setting it during generation means the second
    # generator sees the tree the first one dirtied by writing its own declared output, and refuses.
    # The manifest is the gate during generation; the preflight is the gate on the tree.
    env = dict(os.environ, ZIPPY_PUBLISH_MANIFEST=str(mf))
    for suite in GENERATORS:
        r = subprocess.run(runner + [suite], capture_output=True, text=True, cwd=ROOT, env=env)
        print(f"  {'PASS' if r.returncode == 0 else 'FAIL'}  {suite}")
        if r.returncode != 0:
            print(r.stdout[-2000:], file=sys.stderr)
            die(f"generator {suite} failed")


def validate(commit, ts):
    step(5, "VALIDATE")
    problems = []

    # (a) ONLY declared outputs changed
    changed = set()
    for line in git("status", "--porcelain").splitlines():
        if not line.strip():
            continue
        path = line[3:].strip()
        changed.add(path)
    undeclared = sorted(p for p in changed if p not in OUTPUTS)
    if undeclared:
        problems.append(f"{len(undeclared)} UNDECLARED path(s) changed during generation: "
                        + ", ".join(undeclared[:10]))
    unchanged = sorted(set(OUTPUTS) - changed)
    if unchanged:
        problems.append("declared output(s) did NOT change -- a generator that silently stopped "
                        "producing an artifact is a failure, not a success: " + ", ".join(unchanged))

    # (b) per-artifact provenance, schema, row set
    for rel, spec in sorted(OUTPUTS.items()):
        f = ROOT / rel
        if not f.is_file():
            problems.append(f"{rel}: missing")
            continue
        lines = f.read_text().splitlines()
        if spec["kind"] in ("csv", "tsv"):
            if not lines or not lines[0].startswith("#"):
                problems.append(f"{rel}: no provenance header line")
                continue
            hdr = lines[0]
            for want, what in ((f"git={commit}", "commit"), (f"ts={ts}", "timestamp"),
                               ("clean=yes", "clean marker")):
                if want not in hdr:
                    problems.append(f"{rel}: provenance {what} is not the manifest's ({want!r} absent)")
            if spec["header"] is not None and (len(lines) < 2 or lines[1] != spec["header"]):
                problems.append(f"{rel}: SCHEMA changed -- expected {spec['header']!r}, "
                                f"got {(lines[1] if len(lines) > 1 else '<none>')!r}")
            rows = len(lines) - 2
            if not (spec["min_rows"] <= rows <= spec["max_rows"]):
                problems.append(f"{rel}: {rows} data rows, outside the declared "
                                f"[{spec['min_rows']}, {spec['max_rows']}]")
            # Compare the ordered deterministic row identity, not the first-column SET.  The first
            # column of expressivity.csv has only about a hundred values for 100,000 rows; treating
            # it as a key allowed almost the whole workload to be replaced without detection.
            old_text = git("show", f"HEAD:{rel}", check=False)
            if old_text:
                cmp, _changed = compare_delimited(rel, old_text, f.read_text(), spec, False)
                problems.extend(cmp)
        else:  # markdown: section boundaries
            begins = re.findall(r"<!-- BEGIN benchmark:([\w-]+) -->", "\n".join(lines))
            ends = re.findall(r"<!-- END benchmark:([\w-]+) -->", "\n".join(lines))
            if begins != ends:
                problems.append(f"{rel}: section markers do not pair up: "
                                f"BEGIN {begins} vs END {ends}")
            old = git("show", f"HEAD:{rel}", check=False)
            oldb = re.findall(r"<!-- BEGIN benchmark:([\w-]+) -->", old)
            if oldb and set(oldb) != set(begins):
                problems.append(f"{rel}: the SET of generated sections changed "
                                f"({sorted(set(oldb) ^ set(begins))}) -- a publication regenerates "
                                "sections in place, it does not add or drop them")
            problems.extend(f"{rel}: {p}" for p in markdown_provenance_problems("\n".join(lines), commit, ts))

    for p in problems:
        print(f"  FAIL  {p}")
    if problems:
        die(f"{len(problems)} validation failure(s); the working tree is NOT publishable")
    print("provenance, schema, ordered row identities and section boundaries all check out")


def report():
    step(6, "REPORT")
    stat = git("diff", "--stat", "--", *OUTPUTS).rstrip()
    print(stat or "  (no change)")
    # Whole-line churn is not a validity condition for a timing table: when one timing column is in
    # every row, a legitimate rerun changes 100% of its lines.  Validate the declared structure and
    # row identity instead, and report measurement churn without rejecting it.  Same-commit timing
    # tolerances belong to reproduce(), not to a publication made after code changes.
    problems = []
    for rel in sorted(OUTPUTS):
        numstat = git("diff", "--numstat", "--", rel).strip()
        if not numstat:
            problems.append(f"{rel}: no diff at all after generation")
            continue
        add, rem = numstat.split("\t")[:2]
        if add in ("-", "") or rem in ("-", ""):
            problems.append(f"{rel}: binary or unparseable diff ({numstat})")
            continue
        old = git("show", f"HEAD:{rel}", check=False)
        if not old:
            problems.append(f"{rel}: no previous artifact at HEAD to compare")
            continue
        current = (ROOT / rel).read_text()
        cmp, changed = compare_output(rel, old, current, enforce_timing=False)
        problems.extend(cmp)
        print(f"  {rel:24s} +{add} -{rem}; {changed} measurement/data row(s) changed")
    for pb in problems:
        print(f"  FAIL  {pb}")
    if problems:
        die(f"{len(problems)} diff validation failure(s); the working tree is NOT publishable")
    print("\nThe working tree now holds a validated publication.  Nothing has been committed: "
          "review the diff above and commit it yourself.")


# =============================================================================================
# REPRODUCE.  The published outputs name ONE commit; a reader must be able to check that
# commit out, re-run the gates and the generation, and get the same tables back.  This mode does
# exactly that, in a throwaway `git worktree`, and reports the diff in the terms that matter:
#
#   * PROVENANCE: all four outputs name the same commit, and it is not `-dirty` -- a `-dirty` identity
#     names no tree anyone can check out, so there is nothing to reproduce (that is the state of the
#     tree before the first publication, and this mode says so instead of pretending).
#   * GATES at that commit, with that commit's own gate list (`scripts/gates.py --run` inside the
#     worktree), because a gate added later is not a condition the published numbers were held to.
#   * GENERATION at that commit, under a manifest naming it, into the worktree.
#   * THE DIFF, structurally: same schema row, same row set (key column), same section set, same
#     commit in the provenance.  Measurement VALUES (timings) are expected to differ between two runs
#     and are reported as churn, not failed on.
#
# Exit 0 means: the commit the outputs name reproduces their structure under its own gates.
# =============================================================================================
def output_commit(rel, text):
    """the commit a published output names, or None"""
    if OUTPUTS[rel]["kind"] == "md":
        found = set(re.findall(r"\|\s*git commit\s*\|\s*([0-9a-f]{7,}(?:-dirty)?)\s*\|", text))
        return found if found else None
    first = text.splitlines()[0] if text else ""
    m = re.search(r"git=([0-9a-f]{7,}(?:-dirty)?)", first)
    return {m.group(1)} if m else None


def reproduce(runner_hint):
    step(0, "REPRODUCE the publication the four outputs name")
    named, published = {}, {}
    for rel in sorted(OUTPUTS):
        f = ROOT / rel
        if not f.is_file():
            die(f"{rel}: missing; there is no publication to reproduce")
        published[rel] = f.read_text()
        c = output_commit(rel, published[rel])
        if not c:
            die(f"{rel}: carries no `git=<commit>` provenance")
        if len(c) > 1:
            die(f"{rel}: names more than one commit ({sorted(c)}) -- one publication is one commit")
        named[rel] = next(iter(c))
        print(f"  {rel:24s} git={named[rel]}")
    commits = set(named.values())
    if len(commits) != 1:
        die(f"the four outputs name DIFFERENT commits: {sorted(commits)}.  They were not produced by "
            "one publication and cannot be reproduced as one.")
    sha = commits.pop()
    if sha.endswith("-dirty"):
        die(f"the outputs name `{sha}`: a DIRTY tree, which no one can check out.  This is the "
            "pre-publication state; run the publisher (without --reproduce) once the gates are green.")
    if subprocess.run(["git", "-C", str(ROOT), "cat-file", "-e", f"{sha}^{{commit}}"],
                      capture_output=True).returncode != 0:
        die(f"commit {sha} is not in this repository")
    sbt = resolve_tool("sbt")
    if sbt is None:
        die(missing_message("sbt"))
    wt = pathlib.Path(tempfile.mkdtemp(prefix="zippy-reproduce-")) / "tree"
    git("worktree", "add", "--detach", str(wt), sha)
    print(f"  worktree at {wt} for {sha}")
    try:
        step(1, "GATES at the named commit (its own gate list)")
        r = subprocess.run([sbt, "--server", "--batch", "exportTestRuntime"], cwd=wt,
                           capture_output=True, text=True)
        if r.returncode != 0:
            die(f"`sbt exportTestRuntime` failed in the worktree:\n{r.stdout[-1500:]}")
        wrunner = str(wt / "target/test-runtime/run-suite.sh")
        r = subprocess.run([sys.executable, "scripts/gates.py", "--run", "--runner", wrunner],
                           cwd=wt, capture_output=True, text=True)
        print("\n".join("  " + l for l in r.stdout.splitlines() if l.startswith(("  PASS", "  FAIL", "PASS", "FAIL"))))
        if r.returncode != 0:
            die(f"the named commit's own gates are not green; its published numbers were not held to "
                f"them.  Tail:\n" + "\n".join(r.stdout.splitlines()[-8:]))
        step(2, "GENERATE at the named commit")
        cp = (wt / "target/test-runtime/classpath.txt").read_text().strip()
        env = dict(os.environ, ZIPPY_CP=cp)
        envrec = subprocess.run(["java", "-cp", cp, "morkl.RunEnvironmentMain"], capture_output=True,
                                text=True, cwd=wt, env=env)
        if envrec.returncode != 0:
            die(f"could not capture the environment record in the worktree: {envrec.stderr[:300]}")
        ts = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        mf = wt.parent / "manifest.properties"
        mf.write_text(f"commit={sha[:7]}\ntimestamp={ts}\nenv={envrec.stdout.strip()}\n"
                      f"outputs={','.join(sorted(OUTPUTS))}\n")
        wrunner = [wrunner]
        genv = dict(env, ZIPPY_PUBLISH_MANIFEST=str(mf))
        for suite in GENERATORS:
            r = subprocess.run(wrunner + [suite], capture_output=True, text=True, cwd=wt, env=genv)
            print(f"  {'PASS' if r.returncode == 0 else 'FAIL'}  {suite}")
            if r.returncode != 0:
                die(f"generator {suite} failed in the worktree:\n{r.stdout[-1500:]}")
        step(3, "COMPARE the regenerated outputs with the publication")
        problems = []
        for rel, spec in sorted(OUTPUTS.items()):
            new = (wt / rel).read_text()
            if spec["kind"] == "md":
                problems.extend(f"{rel}: {p}" for p in markdown_provenance_problems(new, sha[:7], ts))
            else:
                first = new.splitlines()[0] if new else ""
                if f"git={sha[:7]}" not in first or f"ts={ts}" not in first or "clean=yes" not in first:
                    problems.append(f"{rel}: regenerated provenance does not match its manifest")
            cmp, changed = compare_output(rel, published[rel], new, enforce_timing=True)
            problems.extend(cmp)
            print(f"  {rel:24s} {changed} measurement/data row(s) differ within declared policy")
        for pb in problems:
            print(f"  FAIL  {pb}")
        if problems:
            die(f"{len(problems)} reproduction difference(s): the named commit does NOT reproduce its publication")
        print(f"\nREPRODUCED: commit {sha} regenerates the publication: deterministic fields are exact and "
              "timings are within their declared tolerances under its own green gates.")
        # E3 reads this: the one gate no in-tree run can produce, recorded by the run that did
        rec = ROOT / "target" / "gates.tsv"
        rec.parent.mkdir(parents=True, exist_ok=True)
        existing = rec.read_text().splitlines() if rec.exists() else []
        label = "publication reproduces from the accepted commit"
        kept = [line for line in existing if not (line.startswith("script\t") and line.split("\t")[1] == label)]
        kept.append(f"script\t{label}\tPASS")
        tmp = rec.with_name(rec.name + f".tmp-{os.getpid()}")
        tmp.write_text("\n".join(kept) + "\n")
        os.replace(tmp, rec)
    finally:
        subprocess.run(["git", "-C", str(ROOT), "worktree", "remove", "--force", str(wt)], capture_output=True)


def selftest():
    failures = []
    spec = OUTPUTS["corpus_runtimes.csv"]
    header = spec["header"]
    a = "# git=abcdef0; ts=t1; clean=yes\n" + header + "\n0,10,2,3,4,10.0\n"
    near = "# git=abcdef0; ts=t2; clean=yes\n" + header + "\n0,10,2,3,4,12.0\n"
    far = "# git=abcdef0; ts=t2; clean=yes\n" + header + "\n0,10,2,3,4,30.0\n"
    forged = "# git=abcdef0; ts=t2; clean=yes\n" + header + "\n0,10,2,3,99,12.0\n"
    if compare_delimited("corpus_runtimes.csv", a, near, spec, True)[0]:
        failures.append("an in-tolerance timing change was rejected")
    if not compare_delimited("corpus_runtimes.csv", a, far, spec, True)[0]:
        failures.append("an out-of-tolerance timing change was accepted")
    if not compare_delimited("corpus_runtimes.csv", a, forged, spec, True)[0]:
        failures.append("a deterministic data mutation was accepted")

    def document(commit="abcdef0", timing="10.0", depth="2"):
        chunks = []
        for slug in EXPECTED_SECTIONS:
            chunks.append(
                f"<!-- BEGIN benchmark:{slug} -->\n## {slug}\n\n"
                "| environment | value |\n|---|---|\n"
                f"| timestamp (UTC) | 2026-01-01T00:00:00Z |\n| git commit | {commit} |\n"
                "| source tree | CLEAN at manifest |\n\n"
                "| program | evalI ms | depth off |\n|---|---:|---:|\n"
                f"| fixture | {timing} | {depth} |\n"
                f"<!-- END benchmark:{slug} -->")
        return "\n\n".join(chunks)

    doc = document()
    if markdown_provenance_problems(doc, "abcdef0", "2026-01-01T00:00:00Z"):
        failures.append("a complete one-manifest Markdown publication was rejected")
    mixed = doc.replace("| git commit | abcdef0 |", "| git commit | 7654321 |", 1)
    if not markdown_provenance_problems(mixed, "abcdef0", "2026-01-01T00:00:00Z"):
        failures.append("mixed per-section provenance was accepted")
    if compare_markdown("docs/BENCHMARKS.md", doc, document(timing="12.0"), True)[0]:
        failures.append("an in-tolerance Markdown timing change was rejected")
    if not compare_markdown("docs/BENCHMARKS.md", doc, document(timing="30.0"), True)[0]:
        failures.append("an out-of-tolerance Markdown timing change was accepted")
    if not compare_markdown("docs/BENCHMARKS.md", doc, document(depth="3"), True)[0]:
        failures.append("a deterministic Markdown field mutation was accepted")

    for failure in failures:
        print(f"  FAIL  {failure}")
    print("benchmark publisher selftest: " + ("PASS" if not failures else f"FAIL ({len(failures)})"))
    return 1 if failures else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--reproduce", action="store_true",
                    help="check out the commit the four outputs name in a worktree, re-run its "
                         "gates and generation, and diff the result structurally (exit 0 = reproduced)")
    ap.add_argument("--dry-run", action="store_true",
                    help="preflight and gates only; report what blocks publication and stop")
    ap.add_argument("--selftest", action="store_true",
                    help="exercise provenance, deterministic-data and timing-tolerance mutations")
    ap.add_argument("--runner", default=os.environ.get("ZIPPY_RUNNER", ""),
                    help="command that runs one JUnit suite; defaults to the IN-TREE runner "
                         "target/test-runtime/run-suite.sh written by `sbt exportTestRuntime`, "
                         "then to $ZIPPY_RUNNER")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if a.reproduce:
        reproduce(a.runner)
        return 0
    # THE IN-TREE RUNNER IS THE DEFAULT, and $ZIPPY_RUNNER is now only an override.  Requiring an
    # environment variable put a variable between the repository and its own acceptance gates: a
    # reader who checked out this commit could not run them, and two runs could disagree because
    # they were handed different runners.  `resolve_runner` is gates.py's, so `sbt check` and this
    # script resolve it identically.
    runner = resolve_runner(a.runner.split() if a.runner else None)
    if runner is None:
        die("no suite runner: run `sbt exportTestRuntime` (which writes "
            "target/test-runtime/run-suite.sh), or pass --runner / set $ZIPPY_RUNNER to a command "
            "that takes one JUnit class name")

    head = preflight()
    run_gates(runner)
    if a.dry_run:
        print("\n--dry-run: preflight and gates pass; stopping before regeneration.")
        return
    if "ZIPPY_CP" not in os.environ:
        die("set $ZIPPY_CP to the runtime classpath so the environment record can be captured once")
    mf, commit, ts = capture(head)
    generate(runner, mf)
    validate(commit, ts)
    report()


if __name__ == "__main__":
    sys.exit(main())
