#!/bin/sh
# Discharge every proof obligation with BOTH z3 and vampire (independent cross-validation).
# Every file asserts the NEGATION of its theorem, so per prover:
#   z3 "unsat" / vampire "Refutation found"  = PROVED
#   z3 "sat"                                 = COUNTERMODEL — the stated theorem is FALSE (hard
#                                              failure: a wrong statement must never sit quietly)
#   timeout/unknown on both                  = OPEN
# The verdict per file is written to STATUS.tsv (file <TAB> z3 <TAB> vampire <TAB> verdict) —
# the MACHINE-READABLE source of truth consumed by scripts/check_obligations.py, so an
# admitted-unproved obligation is distinguishable from a proved one by every tool in the repo.
#
# EXPECTED_OPEN lists the admitted-unproved files (see their headers for the attempt log and the
# compensating differential coverage).  A file going OPEN that is NOT in this list fails the run;
# an EXPECTED_OPEN file getting PROVED is reported so the list can be shrunk.
#
# Families:
#   rule certification        — movement-spec rules vs the SET-OF-PATHS denotation
#   impl characterizations    — EAGER TRIE recursion vs the denotation (the homomorphism theorem)
#   threeway_*                — ZIPPER observation = SET-OF-PATHS = EAGER TRIE, per operator
#   laws/law_*                — the optimiser's source-law certificates (see laws/REGISTRY.tsv)
cd "$(dirname "$0")"
EXPECTED_OPEN=" refine_cli refine_cls "
pass=0; fail=0; open_exp=0; cm=0
: > STATUS.tsv
run_family() {
  dir="$1"; shift
  for f in "$@"; do
    path="$dir$f.smt2"
    z3r=$(z3 -T:120 "$path" 2>&1 | tail -1)
    vr=$(/Applications/vampire --input_syntax smtlib2 -t 120s "$path" 2>&1 | grep -q "Refutation found" && echo proved || echo -)
    if [ "$z3r" = "sat" ]; then
      st="COUNTERMODEL"; cm=$((cm+1))
    elif [ "$z3r" = "unsat" ] || [ "$vr" = "proved" ]; then
      st="PROVED"; pass=$((pass+1))
      case "$EXPECTED_OPEN" in *" $f "*) st="PROVED (remove from EXPECTED_OPEN)";; esac
    else
      case "$EXPECTED_OPEN" in
        *" $f "*) st="OPEN (expected; differential-covered — see header)"; open_exp=$((open_exp+1));;
        *) st="OPEN (NEW — unexpected)"; fail=$((fail+1));;
      esac
    fi
    printf "%s\t%s\t%s\t%s\n" "$dir$f" "$z3r" "$vr" "$st" >> STATUS.tsv
    printf "%-32s z3: %-8s vampire: %-8s => %s\n" "$dir$f" "$z3r" "$vr" "$st"
  done
}
run_family "" pointwise wrap1 restriction keyfolds \
         lemma_append_cons lemma_append_nil composition composition_norm \
         impl_union impl_intersection impl_subtraction \
         impl_wrap impl_unwrap impl_head \
         threeway_union threeway_intersection threeway_subtraction \
         threeway_composition_zip threeway_composition_trie \
         threeway_restriction_zip threeway_restriction_trie \
         threeway_tailsunion_trie threeway_tailsinter_trie \
         keys_intersection keys_subtraction keys_composition keys_restriction keys_filter_exact \
         isempty_finite keyfold_tailsinter keyfold_head keyfold_iter join_spec \
         refine_kmerge refine_kinter refine_clu refine_consif \
         refine_cli refine_cls
if [ -d laws ]; then
  run_family "laws/" $(ls laws/law_*.smt2 2>/dev/null | sed 's|laws/||;s|\.smt2$||')
fi
# spatial-type lattice + concretion (see docs/design_spatial_lattice.md).  The lat_* half is
# datatypes+arithmetic, where default-mode vampire has no theory portfolio and predictably times
# out (docs/traps.md) — z3 is the prover of record there; the sp_* half is pure FOL over paths and
# both provers are tried.  Verdicts still land in STATUS.tsv, so a regression is visible.
if [ -d spatial ]; then
  run_family "spatial/" $(ls spatial/*.smt2 2>/dev/null | sed 's|spatial/||;s|\.smt2$||')
fi
echo "-----"
echo "certified: $pass  expected-open: $open_exp  countermodels: $cm  unexpected-open: $fail"
echo "status table: proofs/STATUS.tsv"
[ $fail -eq 0 ] && [ $cm -eq 0 ]
