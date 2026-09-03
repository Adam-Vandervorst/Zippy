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

import argparse, os, pathlib, re, subprocess, sys, tempfile, datetime

ROOT = pathlib.Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------------------------
# THE DECLARED OUTPUTS.  Anything not on this list may not be written during generation, and
# anything on it that does NOT change is reported (a generator that silently stopped producing an
# artifact is a failure too, not a success).
# ---------------------------------------------------------------------------------------------
OUTPUTS = {
    "corpus_runtimes.csv":  dict(kind="csv", header="idx,nodes,nSpace,nPath,uniqueOut,evalI_ms_per1000",
                                 min_rows=900, max_rows=1100),
    "expressivity.csv":     dict(kind="csv", header="uniqueOut,entropy,nEmpty,nSpace,nPath,respSpace,respPath,respFrac,avgSize,nodes",
                                 min_rows=90, max_rows=100_100),
    # THE HEADER WAS `None` HERE, AND THIS IS THE ONE ARTIFACT WITH A KNOWN SCHEMA DRIFT: its own
    # generator records that a `Transformation` column outlived the constructor it counted.  Leaving
    # the schema unchecked on the file whose schema has actually drifted is the wrong place to save
    # effort, so the header is declared and compared like the others.
    "prog_matrix.tsv":      dict(kind="tsv",
                                 # taken from the artifact itself rather than transcribed:
                                 # a hand-copied 19-column tab-separated header is exactly
                                 # the kind of declaration that drifts silently
                                 header="row\tMention\tLiteral\tSingleton\tUnion\tIntersection\tSubtraction\tRestriction\tRaffination\tComposition\tWrap\tUnwrap\tTailsUnion\tTailsIntersection\tRange\tIteration\tConstant\tDeref\tConcat",
                                 min_rows=1, max_rows=500),
    # `header=None` is not "unchecked": a markdown document has no header ROW, and its schema is
    # its SECTION MARKER SET, which the `md` branch of validate() compares against HEAD -- a
    # section that appeared or vanished is a failure there.
    "docs/BENCHMARKS.md":   dict(kind="md",  header=None, min_rows=1, max_rows=100_000),
}

# The suites that PRODUCE the declared outputs.  Each is run once, in one JVM per suite, with the
# manifest in the environment.
#
# ALL FOUR OUTPUTS, NOT THREE.  An earlier revision listed only the three data artifacts, so
# `docs/BENCHMARKS.md` -- which bullet 2 names explicitly -- had no producer at all: stage 5's
# "a declared output did NOT change" check would have failed every publication, and green gates
# would not have helped.  Its five sections come from two suites: GraphBench writes
# subgraph-hoisting, sc-domains, op-graph-backend and pipeline-ablation; TrieBench writes
# executor-scaling.
GENERATORS = ["morkl.CorpusRuntimes", "morkl.ProgramExpressivity", "morkl.ProgramStats",
              "morkl.GraphBench", "morkl.TrieBench"]

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
from gates import GATE_SUITES, GATE_SCRIPTS, script_argv, resolve_runner   # noqa: E402

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
    failed = []
    # the STATIC checkers first: they take seconds, and failing fast on a dangling reference beats
    # discovering it after four prover-backed suites have run
    for label, argv in GATE_SCRIPTS:
        # `script_argv` comes from gates.py with the list, because the list now contains `.sh`
        # gates as well as `.py` ones and `[sys.executable, ...]` silently mis-invokes those.
        r = subprocess.run(script_argv(argv), capture_output=True, text=True, cwd=ROOT)
        print(f"  {'PASS' if r.returncode == 0 else 'FAIL'}  {label}")
        if r.returncode != 0:
            tail = [l.strip() for l in (r.stdout + r.stderr).splitlines() if l.strip()][-6:]
            failed.append((label, tail))
    for suite in GATE_SUITES:
        r = subprocess.run(runner + [suite], capture_output=True, text=True, cwd=ROOT)
        tail = [l for l in r.stdout.splitlines() if "Tests run" in l or "OK (" in l]
        status = "PASS" if r.returncode == 0 else "FAIL"
        print(f"  {status}  {suite:34s} {tail[-1].strip() if tail else ''}")
        if r.returncode != 0:
            # THE FAILING REQUIREMENTS, not the defect notes.  A `DEFECT:` line is the long-form
            # explanation attached to an entry and can run to thousands of characters; printing it
            # here buries the one thing the reader needs, which is WHICH requirement is red.
            lines = [l.strip() for l in r.stdout.splitlines()
                     if ("exceeds the" in l or "UNSOUND" in l or "STALE EVIDENCE" in l)
                     and not l.lstrip().startswith("DEFECT:")]
            failed.append((suite, [l if len(l) <= 200 else l[:197] + "..." for l in lines]))
    total = len(GATE_SUITES) + len(GATE_SCRIPTS)
    if failed:
        print()
        for suite, lines in failed:
            print(f"  {suite}:")
            for l in lines[:12]:
                print("    " + l.strip())
            if len(lines) > 12:
                print(f"    ... and {len(lines) - 12} more")
        die(f"{len(failed)} of {total} acceptance gate(s) FAILED.  The review's requirement is "
            "\"regenerate the artifacts only after all acceptance gates pass\": publishing now would "
            "put numbers in the tree that the next gate fix invalidates.")
    print(f"all {total} gates green")


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
            # THE ROW SET, WHICH IS WHAT THE REQUIREMENT ASKS FOR.  A count range is not a row set:
            # it passes a table whose every row changed identity, which is exactly the failure a
            # provenance check exists to catch.  The set is taken over the KEY COLUMN -- the first
            # field, which is the row's identity in all three data artifacts (`idx`, the first
            # measurement column, the matrix row label) -- and compared against HEAD.  A key that
            # appeared or vanished is reported; a key whose VALUES changed is expected and is what
            # a regeneration is for.
            sep = "\t" if spec["kind"] == "tsv" else ","
            def keyset(text):
                ls = [l for l in text.splitlines() if l.strip() and not l.startswith("#")]
                return {l.split(sep, 1)[0] for l in ls[1:]} if len(ls) > 1 else set()
            old_text = git("show", f"HEAD:{rel}", check=False)
            if old_text:
                was, now = keyset(old_text), keyset(f.read_text())
                gone, added = sorted(was - now), sorted(now - was)
                if gone or added:
                    problems.append(
                        f"{rel}: the ROW SET changed -- {len(gone)} key(s) gone "
                        f"({', '.join(gone[:5])}), {len(added)} added ({', '.join(added[:5])}). "
                        "A regeneration replaces VALUES; a changed row set means the workload or "
                        "the generator changed and the two tables are not comparable.")
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
            if f"git={commit}" not in "\n".join(lines):
                problems.append(f"{rel}: no section carries the manifest's commit")

    for p in problems:
        print(f"  FAIL  {p}")
    if problems:
        die(f"{len(problems)} validation failure(s); the working tree is NOT publishable")
    print("provenance, schema, row sets and section boundaries all check out")


def report():
    step(6, "REPORT")
    stat = git("diff", "--stat", "--", *OUTPUTS).rstrip()
    print(stat or "  (no change)")
    # THE DIFF IS CHECKED, NOT JUST SHOWN.  "Validate ... and the resulting diff before committing
    # them" is a requirement, and an earlier revision only printed `--stat`, which validates
    # nothing.  What is checkable about a benchmark diff without re-running the benchmark is its
    # SHAPE: a regeneration should touch the provenance header and the measurement values of
    # existing rows.  A diff that adds or removes whole rows has already been caught by the row-set
    # check; what is caught here is a diff that touches NOTHING (the generator silently did not
    # run) or that rewrites a file essentially in full (a format change masquerading as new
    # numbers), because both make the published numbers incomparable with the previous commit.
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
        add, rem = int(add), int(rem)
        total = max(1, len(pathlib.Path(ROOT / rel).read_text().splitlines()))
        churn = (add + rem) / (2.0 * total)
        print(f"  {rel:24s} +{add} -{rem}   churn {churn:.0%} of {total} lines")
        if churn > 0.98:
            problems.append(f"{rel}: {churn:.0%} of the file changed -- that is a rewrite rather "
                            "than a regeneration; the new numbers are not comparable with HEAD's")
    for pb in problems:
        print(f"  FAIL  {pb}")
    if problems:
        die(f"{len(problems)} diff validation failure(s); the working tree is NOT publishable")
    print("\nThe working tree now holds a validated publication.  Nothing has been committed: "
          "review the diff above and commit it yourself.")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--dry-run", action="store_true",
                    help="preflight and gates only; report what blocks publication and stop")
    ap.add_argument("--runner", default=os.environ.get("ZIPPY_RUNNER", ""),
                    help="command that runs one JUnit suite; defaults to the IN-TREE runner "
                         "target/test-runtime/run-suite.sh written by `sbt exportTestRuntime`, "
                         "then to $ZIPPY_RUNNER")
    a = ap.parse_args()
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
    main()
