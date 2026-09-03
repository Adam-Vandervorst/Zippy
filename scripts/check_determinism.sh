#!/bin/sh
# ==================================================================================================
# TWO RUNS OF ONE GATE SUITE MUST AGREE ON EVERY COUNTED LINE.
#
# ==WHAT WENT WRONG==
# `sbt test` and `testOnly morkl.SpatialScaleCheck` disagreed on a counted column: the same tree, the
# same assertion, PASSING in one invocation and FAILING-AND-UNDIAGNOSED in the other (build.log,
# round 7).  Every published number in this repository is read off exactly those columns, so a
# column that depends on which other suites ran first is not a measurement.
#
# ==WHAT THIS CHECKS==
# One gate suite, run TWICE in two fresh JVMs through the in-tree runner, with every `CALIBRATION:`
# line of each run captured and diffed.  Byte-identical => the suite's counted output does not depend
# on anything outside its own JVM, which is what `Test / testGrouping` (build.sbt) is for.  This is
# a REGRESSION GATE on that build change, not a proof about the analysis.
#
# ==AND WHAT A DIFFERENCE MEANS, WHICH IS THE POINT==
# The diff is split into two classes and reported separately, because they license opposite
# conclusions:
#
#   PROBE lines   ([[GlobalState.probe]], printed on suite entry/exit by `CalibrationProbe`) —
#                 the process-wide append-only tables: `Interner`, `HeadAtoms`, the literal store,
#                 the trie decode memos, and the two armed flags.
#   COUNTED lines every other `CALIBRATION:` line: the measured intervals, containments and slopes.
#
#   probe differs, counts differ    -> the JVM state differed and is the LEADING candidate.  This is
#                                      the "interner id drift" story, and here it is supported.
#   probe IDENTICAL, counts differ  -> THE ID-DRIFT HYPOTHESIS IS REFUTED for this suite.  The probe
#                                      is total over the process-wide tables (see GlobalState.scala),
#                                      so a difference cannot be coming from them.  RECORD THE NEXT
#                                      CANDIDATE -- wall clock, `System.nanoTime` budgets, HashMap
#                                      iteration order over identity hashes, JIT warm-up -- BEFORE
#                                      changing anything.  Do not "fix" the interner.
#   probe differs, counts identical -> the grouping regressed (a shared JVM) but nothing counted
#                                      moved.  Still a failure: it is the precondition that broke.
#
# ==THE DEFAULT SUITE==
# `morkl.SpatialEventsCheck`, because it is the ONLY suite that emits the counted channel: 161
# `CALIBRATION:` lines (containment, per-component tightness, per-backend slack, the cornerstone
# tables), against 1 for `SpatialCostCheck` -- which is the ENTRY probe and nothing else.  A
# determinism gate that compares one line passes for the wrong reason.  It is also cheap: 13 s
# measured for one run, so twice is ~26 s inside `sbt check`.  Pass another suite as $1 to widen.
#
# Usage:  scripts/check_determinism.sh [suite ...]
#         ZIPPY_RUNNER=<cmd> scripts/check_determinism.sh   to override the in-tree runner
# ==================================================================================================
set -u
cd "$(dirname "$0")/.." || exit 1

SUITES=${*:-morkl.SpatialEventsCheck}
RUNNER=${ZIPPY_RUNNER:-./target/test-runtime/run-suite.sh}

if [ ! -x "$RUNNER" ]; then
  echo "DETERMINISM: no one-suite runner at $RUNNER -- run \`sbt exportTestRuntime\` (or \`sbt check\`,"
  echo "             which depends on it), or set \$ZIPPY_RUNNER." >&2
  exit 2
fi

OUT=$(mktemp -d "${TMPDIR:-/tmp}/determinism.XXXXXX") || exit 1
trap 'rm -rf "$OUT"' EXIT INT TERM HUP
rc=0

# THE SUITE'S EXIT STATUS IS NOT THIS GATE'S VERDICT.  Several gate suites are RED today for reasons
# review item 1 owns (the product-requirement rows), and a determinism gate that inherited their
# status would be reporting item 1's state instead of its own.  What this gate asserts is that the
# two runs AGREE -- a suite that fails identically twice is deterministic, which is exactly the
# property being checked.  A run that could not START (a missing classpath, an OOM) produces no
# CALIBRATION lines at all and is caught by the emptiness check below.
run_once() {  # $1 = suite, $2 = output file -> prints the CALIBRATION line count
  # `^CALIBRATION:` EXACTLY, so a suite can declare a non-deterministic-by-design channel by giving
  # it a different prefix.  There is one: `CALIBRATION-WALLCLOCK:`, the per-cornerstone optimise
  # time, which used to sit inside the `CALIBRATION:` line and was the ONLY thing that differed
  # between two runs (5 lines of 161; `820 ms` vs `824 ms`).  The rename happened in the suite, not
  # as a filter here -- a filter list in this script is one that grows silently until the gate
  # compares nothing, whereas a prefix is visible at the emitting println.
  "$RUNNER" "$1" 2>&1 | grep '^CALIBRATION:' > "$2"
  wc -l < "$2" | tr -d ' '
}

check_suite() {
  SUITE=$1
  echo "DETERMINISM: $SUITE, twice, through $RUNNER"
  N1=$(run_once "$SUITE" "$OUT/run1")
  echo "  run 1: $N1 CALIBRATION line(s)"
  N2=$(run_once "$SUITE" "$OUT/run2")
  echo "  run 2: $N2 CALIBRATION line(s)"

  if [ "$N1" = "0" ] || [ "$N2" = "0" ]; then
    echo
    echo "DETERMINISM FAILED: a run of $SUITE produced NO \`CALIBRATION:\` lines, so nothing was"
    echo "  compared.  A gate that compares nothing passes for the wrong reason.  Either the suite"
    echo "  could not start, or it no longer prints a probe -- check that it mixes in"
    echo "  \`CalibrationProbe\`."
    rc=1
    return
  fi

  if diff -u "$OUT/run1" "$OUT/run2" > "$OUT/diff"; then
    echo "  DETERMINISM OK: both runs agree on all $N1 CALIBRATION lines."
    return
  fi

  # Classify the difference: only the diff's changed CALIBRATION lines, not its file headers.
  grep -E '^[+-]CALIBRATION' "$OUT/diff" | grep -v '^[+-][+-][+-]' > "$OUT/changed"
  PROBE_DIFF=$(grep -c 'CALIBRATION: PROBE ' "$OUT/changed")
  COUNT_DIFF=$(grep -v 'CALIBRATION: PROBE ' "$OUT/changed" | grep -c 'CALIBRATION')

  echo
  echo "DETERMINISM FAILED: the two runs of $SUITE disagree."
  echo "  probe lines differing:   $PROBE_DIFF"
  echo "  counted lines differing: $COUNT_DIFF"
  echo
  if [ "$PROBE_DIFF" -eq 0 ] && [ "$COUNT_DIFF" -gt 0 ]; then
    echo "  THE ID-DRIFT HYPOTHESIS IS REFUTED HERE.  \`GlobalState.probe\` is identical across the two"
    echo "  runs and it is total over this process's append-only tables (Interner, HeadAtoms and its"
    echo "  two memos, LiteralStore, the three trie decode caches) and over both armed flags -- so"
    echo "  the moving counts are NOT coming from them.  Record the next candidate (wall clock,"
    echo "  nanoTime budgets, identity-hash iteration order, JIT warm-up) in build.log BEFORE"
    echo "  changing code."
  elif [ "$PROBE_DIFF" -gt 0 ] && [ "$COUNT_DIFF" -eq 0 ]; then
    echo "  The per-suite JVM precondition regressed: the process-wide state differs between two runs"
    echo "  of one suite, which \`Test / testGrouping\` exists to prevent.  Nothing counted moved YET."
  else
    echo "  Both moved: the JVM state differed AND the counts followed.  This is the supported form of"
    echo "  the id-drift story -- start from the probe fields that changed."
  fi
  echo
  echo "--- diff (CALIBRATION lines only) ---"
  cat "$OUT/diff"
  rc=1
}

for s in $SUITES; do check_suite "$s"; done
exit $rc
