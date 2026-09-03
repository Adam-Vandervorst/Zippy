#!/bin/sh
# Discharge every RECURSION obligation with z3 AND vampire, recording BOTH verdicts per file.
# The companion of proofs/run.sh, for the recursion-lowering surface: what a Fixpoint computes,
# what each lowering pass preserves, and why each recursion terminates.  terminating/REGISTRY.tsv
# is the TOTAL map from that surface to the files below; this script is what turns it into
# machine-readable status.
#
# Every file asserts the NEGATION of its theorem, staged as one or more push/pop goals, so:
#   z3 "unsat" on every goal / vampire "Refutation found" on every goal = that prover proved it
#   z3 "sat" on any goal   = COUNTERMODEL — the stated theorem is FALSE.  Hard failure: a wrong
#                            statement must never sit quietly (docs/traps.md).
#   timeout/unknown on both = OPEN
# A file is PROVED when EITHER prover discharges ALL of its goals; the z3 and vampire columns of
# STATUS.tsv record which one(s) did, so a single-prover result stays visible instead of being
# implied to be cross-validated.  (Requiring both would flip most of this corpus to OPEN:
# default-mode vampire has no theory portfolio, and half these files carry Int measures — see
# docs/traps.md.  Where cross-validation is load-bearing, the file says so in its header.)
#
# GOAL COUNTS ARE PINNED per file below.  A file that answers "unsat" fewer times than its pin has
# SILENTLY SKIPPED a goal (z3 stops at the first timeout and never reaches the rest — that is
# exactly how the datalog_b_seminaive_lemmas regression hid), and the run fails.  Adding a goal
# without bumping the pin also fails.  Never lower a pin to make a run green.
#
# VAMPIRE AND push/pop.  Vampire has no incremental mode: handed a staged file it conjoins every
# negated goal and one refutation makes it stop, which would NOT be a proof of all of them.  So
# vampire is run ONCE PER GOAL, on the exact assertion stack that goal's (check-sat) sees — every
# depth-0 line plus that one block — reconstructed by the awk program below.
#
# EXPECTED_OPEN lists the admitted-unproved files (their headers carry the attempt log and the
# compensating differential coverage).  A file going OPEN that is NOT in this list fails the run;
# an EXPECTED_OPEN file getting PROVED is reported so the list can be shrunk.
#
# Env: $Z3 / $VAMPIRE pick the binaries (see scripts/toolpath.sh); $Z3_T / $VAMPIRE_T (seconds)
# override the per-goal budgets; VAMPIRE_T=0 skips the vampire leg entirely (z3-only smoke run).
cd "$(dirname "$0")"
. ../scripts/toolpath.sh                       # $Z3 / $VAMPIRE -> PATH -> conventional locations
Z3_BIN=$(resolve_tool z3)           || { echo "$(tool_missing z3)" >&2; exit 1; }
VAMPIRE_BIN=$(resolve_tool vampire) || { echo "$(tool_missing vampire)" >&2; exit 1; }
Z3_T=${Z3_T:-240}
VAMPIRE_T=${VAMPIRE_T:-10}
# transitive_chc.smt2 is NOT in this table on purpose: it is a KEPT NEGATIVE RESULT (an annotated
# failed CHC/Spacer attempt) whose `(check-sat)` answers "sat" by design, and this driver treats a
# "sat" as a countermodel.  It is registered in REGISTRY.tsv with kind FILE and verdict
# NEGATIVE-RESULT so it stays visible without being run as an obligation.
EXPECTED_OPEN=" "

TMP=$(mktemp -d "${TMPDIR:-/tmp}/terminating.XXXXXX") || exit 1
trap 'rm -rf "$TMP"' EXIT INT TERM

# Emit the incremental context of the `goal`-th (1-based) push/pop block: every depth-0 line in
# order (minus its own check-sat), plus the lines of that one block.  That is exactly the
# assertion stack z3 has in scope at that block's (check-sat).
SPLIT='BEGIN { depth = 0; idx = 0 }
/^[ \t]*\(push[ )]/ { depth++; if (depth == 1) idx++; next }
/^[ \t]*\(pop[ )]/  { depth--; next }
{ if (depth == 0) { if ($0 !~ /^[ \t]*\(check-sat\)/) print } else if (idx == goal) print }'

pass=0; fail=0; open_exp=0; cm=0
: > STATUS.tsv

check() {  # file  expected-goal-count
  f=$1; want=$2
  out=$("$Z3_BIN" -T:"$Z3_T" "$f.smt2" 2>&1)
  nz=$(printf '%s\n' "$out" | grep -c '^unsat')
  nsat=$(printf '%s\n' "$out" | grep -c '^sat')
  nerr=$(printf '%s\n' "$out" | grep -cE '^\(error|error ')
  z3col="$nz/$want unsat"
  [ "$nsat" -gt 0 ] && z3col="$z3col, $nsat SAT"
  [ "$nerr" -gt 0 ] && z3col="$z3col, $nerr err"

  if [ "$VAMPIRE_T" -eq 0 ]; then
    vcol="skipped"
    vok=0
  else
    nv=0; g=1
    while [ "$g" -le "$want" ]; do
      awk -v goal="$g" "$SPLIT" "$f.smt2" > "$TMP/goal.smt2"
      if "$VAMPIRE_BIN" --input_syntax smtlib2 -t "${VAMPIRE_T}s" "$TMP/goal.smt2" 2>&1 \
           | grep -q "Refutation found"; then nv=$((nv+1)); fi
      g=$((g+1))
    done
    vcol="$nv/$want proved"
    vok=$([ "$nv" -eq "$want" ] && echo 1 || echo 0)
  fi

  if [ "$nsat" -gt 0 ]; then
    st="COUNTERMODEL"; cm=$((cm+1))
  elif [ "$nerr" -gt 0 ]; then
    st="ERROR (malformed input)"; fail=$((fail+1))
  elif [ "$nz" -eq "$want" ] || [ "$vok" -eq 1 ]; then
    st="PROVED"; pass=$((pass+1))
    case "$EXPECTED_OPEN" in *" $f "*) st="PROVED (remove from EXPECTED_OPEN)";; esac
  else
    case "$EXPECTED_OPEN" in
      *" $f "*) st="OPEN (expected; see header)"; open_exp=$((open_exp+1));;
      *) st="OPEN (NEW — unexpected)"; fail=$((fail+1));;
    esac
  fi
  printf "%s\t%s\t%s\t%s\n" "$f" "$z3col" "$vcol" "$st" >> STATUS.tsv
  printf "%-34s z3: %-16s vampire: %-14s => %s\n" "$f" "$z3col" "$vcol" "$st"
}

# ---- what a Fixpoint computes, and what the lowering passes preserve (O1, O2, O10, O13) -------
check fixpoint_is_lfp                14
check asfixpoint_sound               18
check unroll_vs_kleene               19
check seminaive_correct              21
check tagged_projection              11
check tagged_order                    2
check mono_soundness                 15
check mutual_tagged_bekic             8
check bounded_recursion_residual      5
# ---- the pre-existing termination corpus (T1-T9) ----------------------------------------------
check bounded_growth_decrease         1
check datalog_a_terminates            1
check datalog_b_naive_terminates     15
check datalog_b_seminaive_lemmas      7
check datalog_b_seminaive_terminates  1
check least_fixpoint_unique           1
check no_infinite_descent             3
check reachable_decrease              6
check reachable_value                 1
check scc_decrease                    7
check transitive_equiv                1

# ANNOTATE THE CONDITIONAL VERDICTS.  This harness writes the verdict the PROVER reached, which is
# right.  Whether that verdict is UNQUALIFIED is a separate question, decided by the trusted base in
# docs/TRUSTED.md, and `PROVED` in a table is read as unqualified.  One tool owns that decision so
# the trusted base is not duplicated into each harness; it only ever weakens a verdict, and it is
# idempotent.  See scripts/proof_closure.py.
if command -v python3 >/dev/null 2>&1; then
  python3 ../scripts/proof_closure.py --annotate >/dev/null 2>&1 && \
    echo "conditional verdicts annotated from the trusted base (scripts/proof_closure.py)"
fi

echo "-----"
echo "certified: $pass  expected-open: $open_exp  countermodels: $cm  unexpected-open: $fail"
echo "status table: terminating/STATUS.tsv    obligation map: terminating/REGISTRY.tsv"
[ $fail -eq 0 ] && [ $cm -eq 0 ]
