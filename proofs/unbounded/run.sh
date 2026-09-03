#!/bin/sh
# TIER 3 — THE UNBOUNDED TIER.  Discharge every schematic obligation with vampire, and run the
# two guards that stop a broken encoding from being reported as a corpus of proofs.
#
# WHAT THIS TIER IS.  proofs/*.smt2 certifies INSTANCES (two given programs, one goal, ground or
# nearly so) and terminating/*.p certifies TERMINATION MEASURES.  This directory certifies the
# OPERATOR LAWS THEMSELVES, quantified over all spaces, all paths and all bodies — the statements
# tier-1 (`Lower.sizeBounds`, a syntactic interval per AST node) and tier-2 (`SizeZ3`/`LenZ3`, one
# `(declare-const n<i> Int)` per AST node) cannot express at all.  See _signature.p's header.
#
# THREE THINGS ARE RUN, and all three must pass:
#
#   1. THEOREMS      proofs/unbounded/*.p (files not starting with `_`).  Expected: PROVED.
#                    A file vampire cannot discharge is OPEN and must be listed in EXPECTED_OPEN
#                    with its attempt log in its own header; an unlisted OPEN fails the run.
#                    `SZS status Satisfiable` / `CounterSatisfiable` on a conjecture is a
#                    COUNTERMODEL — the stated theorem is FALSE — and is a hard failure.
#
#   2. NEGATIVE CONTROLS   negative/*.p.  Eight conjectures that are FALSE over `eval`'s
#                    semantics, five of them the exact shape of a bug docs/traps.md records as
#                    having shipped.  Expected: NOT-PROVED.  A refutation here means the encoding
#                    proves too much and EVERY verdict above is void — hard failure.
#
#   3. VACUITY PROBE  each theorem file with its conjecture replaced by `$false`, i.e. the axiom
#                    set alone.  Expected: no refutation.  This is not paranoia: vampire 5.1.0's
#                    built-in integer theory DID derive $false from a plainly consistent
#                    `_signature.p + _card.p` when `card` was `$int`-valued (see _nat.p's header
#                    for the measured evidence), and an inconsistent axiom set proves every
#                    conjecture.  The corpus is arithmetic-free because of it, and this probe is
#                    what keeps it that way.  Skip with VACUITY=0 for a fast re-run.
#
# PROVER MODE.  `--mode casc` (the portfolio), not the default schedule.  MEASURED: `lattice_union`
# — six conjuncts of plain union algebra — is closed in 0.2 s by the portfolio and TIMES OUT at
# 60 s in default saturation mode.  Every timing quoted in a file header is portfolio mode.
#
# ONE PROVER ONLY.  Unlike proofs/run.sh, there is no z3 column: these are quantified first-order
# statements over uninterpreted sorts, and the SMT twin would need `declare-datatypes` for `path`,
# which docs/traps.md 3 records vampire cannot consume — so an SMT-LIB rendering could not be
# cross-checked by the prover that actually discharges this tier.  The negative controls and the
# vacuity probe are the compensating checks, and this limitation is stated in REGISTRY.tsv rather
# than left implicit.
#
# STATUS.tsv (file <TAB> vampire <TAB> probe <TAB> verdict) is the machine-readable source of
# truth, consumed by src/test/scala/UnboundedTier.scala.
cd "$(dirname "$0")" || exit 1
. ../../scripts/toolpath.sh                    # $VAMPIRE -> PATH -> conventional locations
VAMPIRE_BIN=$(resolve_tool vampire) || { echo "$(tool_missing vampire)" >&2; exit 1; }

# Budgets, in seconds.  TLIMIT is sized by the slowest theorem that DOES close (length_compose,
# 39 s measured) plus headroom; only `mon_cancel`, the one admitted-open file, actually spends it.
# NLIMIT and PLIMIT are smaller because their expected outcome is a timeout, so a larger budget
# only lengthens the run: every negative control and every vacuity probe was ALSO run at 60 s and
# 30 s respectively while this corpus was written, with the same outcome.
TLIMIT=${TLIMIT:-180}
NLIMIT=${NLIMIT:-45}
PLIMIT=${PLIMIT:-10}
VACUITY=${VACUITY:-1}

# admitted-unproved, each with its attempt log in its own header.
#
# EMPTY.  `mon_cancel` (left cancellation of append) was the one entry: it needs induction on the
# prefix, `path` is an opaque TFF sort so vampire has no structural-induction rule for it, and the
# conclusion was admitted as the axiom `_cancel.p`, imported by `wrap_roundtrip` and `card_wrap` —
# which were therefore reported PROVED while resting on an admitted domain fact.  It is now PROVED,
# from `_path_induction.p`: the structural-induction SCHEMA for the free term algebra `path`,
# instantiated at that one predicate.  That axiom says nothing about `app`, and both of its
# premises stay obligations (they are `mon_cancel_base` and `mon_cancel_step`, both PROVED).  The
# schema instance is THE trusted item in this tier and it is named as such in REGISTRY.tsv's header
# (it has no row of its own: rows name conjecture files, and it is an axiom module) and in
# docs/atlas.md's acceptance contract.
EXPECTED_OPEN=" "

pass=0; fail=0; open_exp=0; cm=0; neg_ok=0; neg_bad=0; vac_bad=0

szs() {  # last SZS status word, or "none"
  printf '%s\n' "$1" | grep '^% SZS status' | tail -1 | awk '{print $4}'
}

# A FILE THE PROVER COULD NOT READ IS NOT AN UNPROVABLE FILE, AND SCORING IT AS ONE HID A BUG FOR A
# WHOLE ROUND.  Three negative controls used bare `include('_signature.p')` while the loop below
# runs `cd negative`, so vampire reported
#     User error: cannot open file .../negative/_signature.p
# emitted no SZS status at all, and the `*)` arm of the case below recorded
# "NOT-PROVED (expected)" -- a PASS.  A negative control that cannot be parsed pins nothing, so the
# corpus reported three non-vacuity checks it was not performing.  This is checked FIRST now, for
# both loops, and it is a hard failure rather than a verdict.
user_error() {
  printf '%s\n' "$1" | grep -q '^% *User error' || printf '%s\n' "$1" | grep -q '^User error'
}

probe_one() {  # $1 = file, $2 = conjecture name -> "ok" | "VACUOUS"
  [ "$VACUITY" = "0" ] && { echo "skipped"; return; }
  sed "/^tff($2, conjecture,/,\$d" "$1" > .probe.p
  echo 'tff(vacuity_probe, conjecture, $false ).' >> .probe.p
  po=$("$VAMPIRE_BIN" --mode casc -t "${PLIMIT}s" .probe.p 2>&1)
  rm -f .probe.p                      # a temp file left in the corpus directory is a registry desync
  case "$(szs "$po")" in
    Theorem|ContradictoryAxioms|Unsatisfiable) echo "VACUOUS" ;;
    *) echo "ok" ;;
  esac
}

: > STATUS.tsv

for path in *.p; do
  case "$path" in _*) continue;; esac
  f=${path%.p}
  out=$("$VAMPIRE_BIN" --mode casc -t "${TLIMIT}s" "$path" 2>&1)
  st=$(szs "$out")
  # THE SAME CHECK ON THE POSITIVE SIDE, and here it matters even more: an unreadable file scores
  # `OPEN`, and `OPEN` for a name in `EXPECTED_OPEN` is a PASS.  A missing include would therefore
  # be indistinguishable from a hard obligation.
  if user_error "$out"; then
    printf "%s\t%s\t%s\t%s\n" "$f" "${st:-none}" "-" \
      "UNREADABLE — the prover could not load this file" >> STATUS.tsv
    printf "%-26s vampire: %-20s probe: %-8s => %s\n" "$f" "${st:-none}" "-" \
      "UNREADABLE — the prover could not load this file"
    fail=$((fail+1))
    continue
  fi
  probe=$(probe_one "$path" "$f")
  case "$st" in
    Theorem|Unsatisfiable)      v=PROVED ;;
    ContradictoryAxioms)        v=CONTRADICTORY ;;
    Satisfiable|CounterSatisfiable) v=COUNTERMODEL ;;
    *)                          v=OPEN ;;
  esac
  if [ "$probe" = "VACUOUS" ]; then
    verdict="VACUOUS (axioms alone refuted — every verdict from this file is void)"
    vac_bad=$((vac_bad+1))
  elif [ "$v" = "COUNTERMODEL" ]; then
    verdict="COUNTERMODEL"; cm=$((cm+1))
  elif [ "$v" = "CONTRADICTORY" ]; then
    verdict="CONTRADICTORY"; cm=$((cm+1))
  elif [ "$v" = "PROVED" ]; then
    verdict=PROVED; pass=$((pass+1))
    case "$EXPECTED_OPEN" in *" $f "*) verdict="PROVED (remove from EXPECTED_OPEN)";; esac
  else
    case "$EXPECTED_OPEN" in
      *" $f "*) verdict="OPEN (expected; see header attempt log)"; open_exp=$((open_exp+1));;
      *) verdict="OPEN (NEW — unexpected)"; fail=$((fail+1));;
    esac
  fi
  printf "%s\t%s\t%s\t%s\n" "$f" "$st" "$probe" "$verdict" >> STATUS.tsv
  printf "%-26s vampire: %-20s probe: %-8s => %s\n" "$f" "$st" "$probe" "$verdict"
done

echo "----- negative controls (MUST NOT be provable)"
for path in negative/*.p; do
  f=$(basename "$path" .p)
  out=$(cd negative && "$VAMPIRE_BIN" --mode casc -t "${NLIMIT}s" "$f.p" 2>&1)
  st=$(szs "$out")
  if user_error "$out"; then
    verdict="UNREADABLE — the prover could not load this file, so the control pins NOTHING"
    st="${st:-none}"
    neg_bad=$((neg_bad+1))
  else
  case "$st" in
    Theorem|Unsatisfiable|ContradictoryAxioms)
      verdict="PROVED — ENCODING IS BROKEN"; neg_bad=$((neg_bad+1)) ;;
    *) verdict="NOT-PROVED (expected)"; neg_ok=$((neg_ok+1)) ;;
  esac
  fi
  printf "%s\t%s\t%s\t%s\n" "negative/$f" "$st" "-" "$verdict" >> STATUS.tsv
  printf "%-26s vampire: %-20s          => %s\n" "negative/$f" "$st" "$verdict"
done

rm -f .probe.p

# ANNOTATE THE CONDITIONAL VERDICTS.  This loop writes the verdict THE PROVER REACHED, which is
# right -- the prover is what ran.  But `PROVED` in a table is read as unqualified, and for a result
# whose transitive `include` closure reaches a trusted assumption (docs/TRUSTED.md) that reading is
# wrong: `mon_cancel` is proved from `_path_induction.p`, an induction SCHEMA first-order logic
# cannot state, so it is conditional and the table has to say so.  Duplicating the trusted base into
# this script so it could annotate as it goes would give two copies to drift apart, so the closure is
# computed from the proof files by one tool and applied here, after the run.
if command -v python3 >/dev/null 2>&1; then
  python3 ../../scripts/proof_closure.py --annotate >/dev/null 2>&1 &&     echo "conditional verdicts annotated from the include closure (scripts/proof_closure.py)"
fi

echo "-----"
echo "certified: $pass  expected-open: $open_exp  unexpected-open: $fail  countermodels/contradictions: $cm"
echo "negative controls held: $neg_ok  BROKEN: $neg_bad   vacuous axiom sets: $vac_bad"
echo '  NOTE: "certified" counts PROVER verdicts.  Whether a verdict is UNQUALIFIED is a different'
echo '  question, decided by the include closure: run `python3 scripts/proof_closure.py` for the'
echo '  per-result answer and the trusted entries each one reaches.'
echo "status table: proofs/unbounded/STATUS.tsv   registry: proofs/unbounded/REGISTRY.tsv"
[ $fail -eq 0 ] && [ $cm -eq 0 ] && [ $neg_bad -eq 0 ] && [ $vac_bad -eq 0 ]
