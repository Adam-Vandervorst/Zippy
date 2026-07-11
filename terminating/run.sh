#!/bin/sh
# Z3 cross-check of every termination lemma: each .smt2 is the SMT-LIB twin of the same-named
# TPTP file (.p), with staged files carrying several push/pop goals.  Every check-sat must
# answer "unsat" (a "sat" would be a COUNTERMODEL to the stated lemma; unknown/timeout fails).
# Expected goal counts per file are pinned below so a silently-skipped goal also fails.
cd "$(dirname "$0")"
fail=0
check() {  # file expected-unsat-count
  out=$(z3 -T:240 "$1.smt2" 2>&1)
  n=$(printf '%s\n' "$out" | grep -c '^unsat')
  bad=$(printf '%s\n' "$out" | grep -cE '^sat|^unknown|^timeout|error')
  if [ "$n" -eq "$2" ] && [ "$bad" -eq 0 ]; then st="OK ($n/$2 unsat)"
  else st="FAIL (unsat $n/$2, bad $bad)"; fail=1; fi
  printf "%-36s %s\n" "$1" "$st"
}
check bounded_growth_decrease 1
check datalog_a_terminates 1
check datalog_b_naive_terminates 15
check datalog_b_seminaive_lemmas 4
check datalog_b_seminaive_terminates 1
check least_fixpoint_unique 1
check no_infinite_descent 3
check reachable_decrease 6
check reachable_value 1
check scc_decrease 7
check transitive_equiv 1
exit $fail
