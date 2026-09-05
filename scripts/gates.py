#!/usr/bin/env python3
"""THE ONE ACCEPTANCE-GATE LIST.

WHY THIS FILE EXISTS.  The gate list was duplicated between the publisher and development prose,
and the copies disagreed -- an earlier revision of the publisher listed
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

import argparse, datetime, os, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# The generated in-tree runner: one munit suite, one plain forked JVM, the same java options
# `Test / fork` uses.  `sbt exportTestRuntime` writes it; `sbt check` depends on that task.
DEFAULT_RUNNER = ROOT / "target" / "test-runtime" / "run-suite.sh"

# ---------------------------------------------------------------------------------------------
# THE SCALA GATE SUITES.  The first four cover operational semantics and resource analysis;
# the B1/B2 suites are the decision layer's acceptance.
# ---------------------------------------------------------------------------------------------
GATE_SUITES = [
    "morkl.SpatialCostCheck",
    "morkl.SpatialEventsCheck",
    "morkl.SpatialScaleCheck",
    "morkl.SpatialPipelineCheck",
    # Residual alternatives are explicit and evaluation-free; selection is by certified
    # dominance, deterministic, and every removal replays through scripts/check_selection.py
    "morkl.AlternativesCheck",
    "morkl.ParetoCheck",
    # Decision cases: certified choice, counted containment, scalar predictors compared.
    "morkl.DecisionsCheck",
    # the acceptance suites of the spine, registered so docs/ACCEPTANCE.md can be generated from gate results
    "morkl.SpatialSemanticsCheck",   # A1
    "morkl.DeltaIRCheck",            # A2
    "morkl.SpatialDomainCheck",      # A3
    "morkl.CrossFunctionCostCheck",  # A5
    "morkl.ProofTraceCheck",         # C3
    "morkl.EquivPipelineTest",       # D2 (verify mode: every committed pipeline artifact matches)
    "morkl.MutationGates",           # E1
    "morkl.Puzzle15Check",           # D3 (verify mode: the committed puzzle15 artifacts match)
]

# ---------------------------------------------------------------------------------------------
# THE SCRIPT GATES.  Each is (label, argv-relative-to-scripts/).  A `.py` entry is run with
# python3; anything else is run directly, so a `.sh` gate needs no special case here.
#
# `check_determinism.sh` runs one suite twice and therefore consumes the same explicit runner as
# the suite loop. `check_lean.sh` builds every theorem used by the proof closure.
# ---------------------------------------------------------------------------------------------
GATE_SCRIPTS = [
    ("reference checking on one snapshot",
     ["check_references.py", "--snapshot=index", "--strict"]),
    ("reference-checker self-test", ["check_references.py", "--selftest"]),
    ("benchmark publication checker self-test", ["publish_benchmarks.py", "--selftest"]),
    ("pipeline marker/declaration audit", ["audit_pipeline_markers.py"]),
    ("typed proof traces: every declared cell resolves to a checked DAG", ["check_traces.py"]),
    ("law certificates discharged", ["check_laws.py"]),
    ("cited obligations discharged", ["check_obligations.py"]),
    ("counted columns are run-order independent", ["check_determinism.sh"]),
    ("mechanized theorems build", ["check_lean.sh"]),
    # AFTER check_lean.sh, and not before: the closure check lifts a `PROVED-MODULO` row only on the
    # strength of the witness `check_lean.sh` writes (`target/lean-mechanized.tsv`), so on a clean
    # checkout the closure check run FIRST reports every mechanized row as a problem.  Measured
    # (2026-09-04): 4 problems on a fresh clone with the tables byte-identical to a passing run.
    # the assert-level closure of the SMT tiers writes target/assert-closure.tsv, which the closure
    # check below reads; an unclassified assert fails here.
    ("every SMT assert classified: goal, definition, derived, or a named assumption",
     ["check_asserts.py"]),
    ("proof status vs the trusted base, one dependency graph over the traces", ["proof_closure.py", "--check"]),
    # Everything below consumes target/trace-closure.tsv.  Keep it after proof_closure.py: a clean
    # checkout has no target table, while a warm checkout may contain a stale one.  Running a
    # consumer first made the same commit fail clean and pass warm.
    ("pipeline claims accepted: no SINGLE-SIDE, BUDGET or chained cell", ["audit_pipeline_markers.py", "--accept"]),
    # C4's acceptance as a gate: marking O6a open must turn every trace that unfolds or folds conditional
    ("trust closure mutation: an injected open O6a reaches its consumers",
     ["proof_closure.py", "--inject-open", "O6a", "--expect-consumers", "1"]),
    # B2/B3: every committed selection certificate re-derives from its own candidate rows
    ("selection certificates replay independently", ["check_selection.py", "proofs/decisions", "proofs/pipeline/resources"]),
    ("structural coverage: every feature inside a checked chain, census complete", ["check_coverage.py"]),
    ("structural coverage mutations are caught", ["check_coverage.py", "--selftest"]),
    ("cornerstone resource certificates contain their counted runs; selections replay", ["check_resources.py"]),
    ("puzzle15: legal expansion, counted runs inside, bounds under the proved maximum, thresholds", ["check_puzzle15.py"]),
    # E3: the acceptance document is derived from the gate record this run writes (see main: the record is
    # written BEFORE these two run, so `--check` sees this run's results)
    ("acceptance mutations move their rows", ["gen_acceptance.py", "--selftest"]),
    # This one consumes the current run's target/gates.tsv. main() deliberately excludes it from
    # run_scripts(), writes the current record, runs it, then atomically rewrites the final record.
    ("acceptance status agrees with the evidence", ["gen_acceptance.py", "--check"]),
]

ACCEPTANCE_STATUS_GATE = "acceptance status agrees with the evidence"


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


def run_scripts(entries=None, runner=None, verbose=True):
    """The selected script gates, in order. Returns [(label, rc, output)] for failures."""
    failed = []
    env = None if runner is None else dict(os.environ, ZIPPY_RUNNER=runner[0])
    for label, argv in (GATE_SCRIPTS if entries is None else entries):
        r = subprocess.run(script_argv(argv), capture_output=True, text=True, cwd=ROOT, env=env)
        if verbose:
            print(f"  {'PASS' if r.returncode == 0 else 'FAIL'}  {label}", flush=True)
        if r.returncode != 0:
            failed.append((label, r.returncode, (r.stdout + r.stderr).strip().splitlines()))
    return failed


def write_record(path, failed, suites_ran, pending=()):
    """Atomically write the exact status of this run; never leave a previous or partial record."""
    failed_names = {name for name, _, _ in failed}
    pending_names = set(pending)
    rec = pathlib.Path(path)
    rec.parent.mkdir(parents=True, exist_ok=True)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    tmp = rec.with_name(rec.name + f".tmp-{os.getpid()}")
    with tmp.open("w") as f:
        f.write(f"# gate results\t{stamp}\n# kind\tname\tstatus\n")
        for label, _argv in GATE_SCRIPTS:
            status = "NOT-RUN" if label in pending_names else "FAIL" if label in failed_names else "PASS"
            f.write(f"script\t{label}\t{status}\n")
        for suite in GATE_SUITES:
            status = "NOT-RUN" if not suites_ran else "FAIL" if suite in failed_names else "PASS"
            f.write(f"suite\t{suite}\t{status}\n")
    os.replace(tmp, rec)
    return rec


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
    ap.add_argument("--record", default=str(ROOT / "target" / "gates.tsv"),
                    help="where to write one PASS/FAIL/NOT-RUN row per gate (read by scripts/gen_acceptance.py)")
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
    # All scripts except the final status comparison run first in dependency order. The comparison is
    # later: it consumes the record containing THIS run's script and suite results.
    ordinary_scripts = [e for e in GATE_SCRIPTS if e[0] != ACCEPTANCE_STATUS_GATE]
    status_entry = next(e for e in GATE_SCRIPTS if e[0] == ACCEPTANCE_STATUS_GATE)
    runner = resolve_runner(a.runner)
    if runner is None:
        print(f"\nGATES ABORTED: no one-suite runner at {DEFAULT_RUNNER.relative_to(ROOT)}.\n"
              f"Run `sbt exportTestRuntime` (or `sbt check`, which depends on it).")
        return 2
    failed = run_scripts(ordinary_scripts, runner=runner)
    suites_ran = False
    if not a.scripts_only:
        failed += run_suites(runner)
        suites_ran = True
    # First record all evidence the acceptance document actually depends on. The status comparison
    # is pending, not optimistically PASS. After --check reads the record, rewrite it with the result.
    rec = write_record(a.record, failed, suites_ran, pending=[ACCEPTANCE_STATUS_GATE])
    failed += run_scripts([status_entry], runner=runner)
    rec = write_record(a.record, failed, suites_ran)
    print(f"\nrecorded to {rec.relative_to(ROOT) if rec.is_relative_to(ROOT) else rec}")

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
