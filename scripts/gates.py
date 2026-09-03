#!/usr/bin/env python3
"""THE ONE ACCEPTANCE-GATE LIST.

WHY THIS FILE EXISTS.  The gate list was duplicated: `scripts/publish_benchmarks.py` held one copy
and `plan.md` prose held another, and they disagreed -- an earlier revision of the publisher listed
only the four Scala suites, so item 7's declared gate (`check_references.py --strict`) and item 8's
(`proof_closure.py --check`) were never run by the thing that gates publication.  A gate an item
declares for itself and the publisher does not run is not a gate.  So the list lives HERE, once, and
both entry points import it:

    sbt check                   -> `python3 scripts/gates.py --run` (see build.sbt)
    publish_benchmarks.py       -> `from gates import GATE_SUITES, GATE_SCRIPTS`

AND NO ENVIRONMENT VARIABLES.  Running a suite used to need `--runner` or `$ZIPPY_RUNNER` handed in
from outside, which put an environment variable between the repository and its own gates: a reader
who checks out this commit could not run them, and two runs could disagree because they were given
different runners.  `sbt exportTestRuntime` (build.sbt) writes an in-tree runner at
`target/test-runtime/run-suite.sh` and that is the default, so `--runner` is now an override rather
than a requirement.
"""

import argparse, os, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# The generated in-tree runner: one munit suite, one plain forked JVM, the same java options
# `Test / fork` uses.  `sbt exportTestRuntime` writes it; `sbt check` depends on that task.
DEFAULT_RUNNER = ROOT / "target" / "test-runtime" / "run-suite.sh"

# ---------------------------------------------------------------------------------------------
# THE SCALA GATE SUITES.  These four are review item 1's declared gate and the publisher's.
# ---------------------------------------------------------------------------------------------
GATE_SUITES = [
    "morkl.SpatialCostCheck",
    "morkl.SpatialEventsCheck",
    "morkl.SpatialScaleCheck",
    "morkl.SpatialPipelineCheck",
]

# ---------------------------------------------------------------------------------------------
# THE SCRIPT GATES.  Each is (label, argv-relative-to-scripts/).  A `.py` entry is run with
# python3; anything else is run directly, so a `.sh` gate needs no special case here.
#
# The first six are the pre-existing set that `publish_benchmarks.py` held.  The last two are
# Phase 0's own gates, added here rather than left as prose for the reason in this file's header:
#   - check_determinism.sh (0.2) -- two runs of one gate suite must agree on every CALIBRATION line.
#   - check_lean.sh        (0.5) -- `lake build` over proofs/lean, which is where items 3 and 8
#                                   put every mechanized theorem.
# ---------------------------------------------------------------------------------------------
GATE_SCRIPTS = [
    ("reference checking on one snapshot (item 7)",
     ["check_references.py", "--snapshot=index", "--strict"]),
    ("reference-checker self-test (item 7)", ["check_references.py", "--selftest"]),
    ("proof status vs the trusted base (item 8)", ["proof_closure.py", "--check"]),
    ("pipeline marker/declaration audit (item 4)", ["audit_pipeline_markers.py"]),
    ("law certificates discharged (item 3/4)", ["check_laws.py"]),
    ("cited obligations discharged (item 3/4)", ["check_obligations.py"]),
    ("counted columns are run-order independent (0.2)", ["check_determinism.sh"]),
    ("mechanized theorems build (0.5)", ["check_lean.sh"]),
]


def gate_count():
    return len(GATE_SUITES) + len(GATE_SCRIPTS)


def script_argv(argv):
    """the command line for one script gate, resolved against scripts/"""
    head, rest = argv[0], argv[1:]
    path = str(ROOT / "scripts" / head)
    return ([sys.executable, path] if head.endswith(".py") else [path]) + rest


def resolve_runner(explicit=None):
    """the one-suite runner, or None with the reason printed by the caller"""
    if explicit:
        return [explicit] if isinstance(explicit, str) else list(explicit)
    if DEFAULT_RUNNER.is_file() and os.access(DEFAULT_RUNNER, os.X_OK):
        return [str(DEFAULT_RUNNER)]
    return None


def run_scripts(verbose=True):
    """every script gate, in order.  Returns [(label, rc, output)] for the failures."""
    failed = []
    for label, argv in GATE_SCRIPTS:
        r = subprocess.run(script_argv(argv), capture_output=True, text=True, cwd=ROOT)
        if verbose:
            print(f"  {'PASS' if r.returncode == 0 else 'FAIL'}  {label}", flush=True)
        if r.returncode != 0:
            failed.append((label, r.returncode, (r.stdout + r.stderr).strip().splitlines()))
    return failed


# The JUnit verdict line, and the lines that name a FAILING REQUIREMENT.  Both are picked out
# explicitly rather than taken as "the tail", because the tail is now the `CalibrationProbe` EXIT
# probe -- a 200-character line of interner sizes, which is the least useful thing to put beside a
# PASS/FAIL.  And a suite's own failure text runs to hundreds of lines of which four say `FAILURES!!!`
# and the rest are stack frames; what a reader needs is WHICH requirement is red.
VERDICT = re.compile(r"^(Tests run:|OK \()")
REQUIREMENT_FAILURE = re.compile(
    r"exceeds the |UNSOUND|STALE (EVIDENCE|FIGURE)|LEDGER COVERAGE|NO EVIDENCE ENTRY|"
    r"product-requirement FAILURE")


def run_suites(runner, verbose=True):
    """every gate suite, one forked JVM each.  Returns [(suite, rc, output)] for the failures."""
    failed = []
    for suite in GATE_SUITES:
        r = subprocess.run(runner + [suite], capture_output=True, text=True, cwd=ROOT)
        lines = [l.rstrip() for l in (r.stdout + r.stderr).splitlines() if l.strip()]
        verdict = next((l.strip() for l in reversed(lines) if VERDICT.match(l.strip())), "")
        if verbose:
            print(f"  {'PASS' if r.returncode == 0 else 'FAIL'}  {suite:34s} {verdict}", flush=True)
        if r.returncode != 0:
            # the requirement failures if there are any, else the tail (a crash, an OOM, a missing
            # class -- all of which report nothing that matches, and all of which need the tail)
            named = [l.strip() for l in lines
                     if REQUIREMENT_FAILURE.search(l) and not l.lstrip().startswith("DEFECT:")]
            failed.append((suite, r.returncode, ([verdict] + named) if named else lines[-25:]))
    return failed


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--run", action="store_true", help="run every gate; exit non-zero on any failure")
    ap.add_argument("--list", action="store_true", help="print the gate list and exit")
    ap.add_argument("--runner", help="override the one-suite runner "
                                     "(default: target/test-runtime/run-suite.sh)")
    ap.add_argument("--scripts-only", action="store_true", help="skip the Scala suites")
    a = ap.parse_args()

    if a.list or not a.run:
        print(f"{gate_count()} acceptance gates\n")
        for label, argv in GATE_SCRIPTS:
            print(f"  script  {label}\n            {' '.join(argv)}")
        for s in GATE_SUITES:
            print(f"  suite   {s}")
        r = resolve_runner(a.runner)
        print(f"\nrunner: {' '.join(r) if r else 'ABSENT — run `sbt exportTestRuntime`'}")
        return 0

    # THE COUNT IS WHAT ACTUALLY RAN.  With `--scripts-only` it reported "all 12 gates green" after
    # running 8, which is the shape of claim this repository exists not to make.
    ran = len(GATE_SCRIPTS) + (0 if a.scripts_only else len(GATE_SUITES))
    scope = "" if ran == gate_count() else f" of {gate_count()} (--scripts-only: the Scala suites are skipped)"
    print(f"=== {ran} ACCEPTANCE GATES{scope} ===", flush=True)
    # SCRIPTS FIRST, and this order is deliberate: they cost seconds and the suites cost minutes, so
    # a broken reference or an unqualified PROVED is reported before a prover-backed suite has run.
    failed = run_scripts()
    if not a.scripts_only:
        runner = resolve_runner(a.runner)
        if runner is None:
            print(f"\nGATES ABORTED: no one-suite runner at {DEFAULT_RUNNER.relative_to(ROOT)}.\n"
                  f"Run `sbt exportTestRuntime` (or `sbt check`, which depends on it).")
            return 2
        failed += run_suites(runner)

    if failed:
        print(f"\n{len(failed)} of {ran} gate(s) FAILED:")
        for name, rc, lines in failed:
            print(f"\n  {name}  (exit {rc})")
            for l in lines[:40]:
                print(f"    {l if len(l) <= 200 else l[:197] + '...'}")
            if len(lines) > 40:
                print(f"    ... and {len(lines) - 40} more")
        return 1
    print(f"\nall {ran} gates green" +
          ("" if ran == gate_count() else f"; {gate_count() - ran} NOT RUN (--scripts-only)"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
