#!/bin/sh
# Discharge the SPATIAL-SEMANTIC obligations (review.md finding 6: γ, α, the order, and the
# per-operator may/must rules) and write proofs/spatial-semantic/STATUS.tsv.
#
# Every file asserts the NEGATION of its theorem, so per prover:
#   z3 "unsat"                       = PROVED
#   z3 "sat"                         = COUNTERMODEL — the STATEMENT is false.  This is a hard
#                                      failure: three of the twenty statements below were wrong on
#                                      the first pass and z3 said so (the models had omitted
#                                      `Shape.mk`'s weakening of `otherTail` and the code's may-ε
#                                      branch in `restrict`), which is the whole point of writing
#                                      them down.
#   timeout/unknown                  = OPEN
#
# Both provers are run and BOTH verdicts are recorded, as proofs/run.sh does.  Every obligation here
# is QUANTIFIER-FREE over datatypes + linear arithmetic, so z3 is the prover of record; default-mode
# vampire has no theory portfolio (docs/traps.md) and is expected to be inconclusive on most files.
# A file is labelled PROVED when EITHER prover succeeds, and the columns show which.
#
# This script writes ONLY proofs/spatial-semantic/STATUS.tsv.  It does not touch proofs/STATUS.tsv,
# so the two corpora stay independently auditable.
cd "$(dirname "$0")"
pass=0; cm=0; open=0
: > STATUS.tsv
for path in gsem_*.smt2; do
  f=$(basename "$path" .smt2)
  z3r=$(z3 -T:60 "$path" 2>&1 | tail -1)
  vr=$(/Applications/vampire --input_syntax smtlib2 -t 60s "$path" 2>&1 | grep -q "Refutation found" && echo proved || echo -)
  if [ "$z3r" = "sat" ]; then
    st="COUNTERMODEL"; cm=$((cm+1))
  elif [ "$z3r" = "unsat" ] || [ "$vr" = "proved" ]; then
    st="PROVED"; pass=$((pass+1))
  else
    st="OPEN"; open=$((open+1))
  fi
  printf "%s\t%s\t%s\t%s\n" "$f" "$z3r" "$vr" "$st" >> STATUS.tsv
  printf "%-40s z3: %-8s vampire: %-8s => %s\n" "$f" "$z3r" "$vr" "$st"
done
echo "-----"
echo "proved: $pass  countermodels: $cm  open: $open"
echo "status table: proofs/spatial-semantic/STATUS.tsv"
[ $cm -eq 0 ] && [ $open -eq 0 ]
