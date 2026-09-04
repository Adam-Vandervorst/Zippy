#!/bin/sh
# ==================================================================================================
# THE LEAN GATE.  `lake build` over `proofs/lean`, plus the two things a build alone does not say.
#
# ==WHY IT IS A GATE AND NOT A NOTE==
# plan.md items 3 and 8 make a Lean-checked theorem a PRECONDITION of any unqualified `PROVED` for
# the substitution and fixpoint claims: `docs/TRUSTED.md` T1 is an induction SCHEMA that first-order
# logic cannot state, T2 is four induction principles asserted inside one SMT file, and T3 admits
# Kruskal's tree theorem outright.  A mechanized theorem that has stopped compiling is not a weaker
# claim than before -- it is the SAME claim with nothing behind it, and the status tables would go on
# reporting it.  So the build is one of `sbt check`'s gates (scripts/gates.py), and this script is
# what that gate runs.
#
# ==WHAT IT CHECKS, IN ORDER==
#   1. `lake` resolves through toolchain.conf (env $LAKE -> $ZIPPY_TOOLS -> PATH -> elan's root).
#   2. THE TOOLCHAIN PIN MATCHES WHAT IS INSTALLED.  `proofs/lean/lean-toolchain` names a Lean
#      version; if elan does not have it, `lake` silently downloads a second toolchain, which turns a
#      gate into a network operation and can leave the package building against a Lean the tree never
#      declared.  This is checked BEFORE the build and reported as its own failure.
#   3. `lake build` -- the whole package, from `Zippy.lean`'s import closure.
#   4. EVERY `% MECHANIZED-IN:` MARKER RESOLVES.  A proof file may carry
#          % MECHANIZED-IN: proofs/lean/Zippy/Pointwise.lean#Zippy.Space.unwrap_wrap
#      which is what lets `scripts/proof_closure.py` lift that file's row from `PROVED-MODULO T1` to
#      unqualified `PROVED`.  A marker naming a file that does not exist, or a theorem that is not in
#      it, would lift a status on the strength of a typo -- so every marker is resolved here and an
#      unresolved one FAILS.  (`proof_closure.py --check` refuses to lift anything when this script
#      has not been run, so the two cannot disagree in the lenient direction.)
#   5. THE AXIOM AUDIT.  For each marked theorem, `#print axioms` lists what it actually depends on.
#      A theorem closed with `sorry` still BUILDS -- with a warning that a log filter can lose -- and
#      would then be lifting a status while proving nothing.  `sorryAx` in the axiom list is a hard
#      failure; the rest of the list is printed, so `2E.6`'s requirement ("check_lean.sh lists the
#      axioms each theorem uses and they are exactly Lean's") has its output from the start.
#
# Usage:  scripts/check_lean.sh              the gate
#         scripts/check_lean.sh --probe-kruskal
#             answers plan.md's named TOOLCHAIN RISK for 2E.3 -- is Kruskal's tree theorem (or
#             Higman's lemma) in the pinned Mathlib?  Reported, never asserted: 2E.3 has to know
#             before it starts, and the fallback is proving Kruskal from Higman.
# ==================================================================================================
set -u
cd "$(dirname "$0")/.." || exit 1
ROOT=$(pwd)
LEAN_DIR=$ROOT/proofs/lean

. "$ROOT/scripts/toolpath.sh"                  # $LAKE -> $ZIPPY_TOOLS -> PATH -> elan's root
LAKE_BIN=$(resolve_tool lake) || { echo "LEAN: $(tool_missing lake)" >&2; exit 1; }

fail() { echo; echo "LEAN GATE FAILED: $*"; exit 1; }

# ---- 1/2. the pin ---------------------------------------------------------------------------------
[ -f "$LEAN_DIR/lean-toolchain" ] || fail "proofs/lean/lean-toolchain is missing; the package has no pin"
WANT=$(tr -d ' \t\r\n' < "$LEAN_DIR/lean-toolchain")
# elan stores a toolchain as leanprover--lean4---v4.33.1 for leanprover/lean4:v4.33.1
WANT_DIR=$(printf '%s' "$WANT" | sed 's|/|--|g; s|:|---|g')
ELAN_ROOT=${ELAN_HOME:-$HOME/.elan}
echo "LEAN: lake      $LAKE_BIN"
echo "LEAN: pinned to $WANT"
if [ -d "$ELAN_ROOT/toolchains/$WANT_DIR" ]; then
  echo "LEAN: toolchain $WANT_DIR is INSTALLED"
else
  echo "LEAN: installed toolchains: $(ls "$ELAN_ROOT/toolchains" 2>/dev/null | tr '\n' ' ')"
  fail "proofs/lean/lean-toolchain pins \`$WANT\` and elan does not have it.  Building would download
  a second toolchain, which makes this gate a network operation.  Either install it
  (\`elan toolchain install $WANT\`) or re-pin the package to an installed one -- and if you re-pin,
  re-pin Mathlib's \`rev\` in proofs/lean/lakefile.toml to the SAME version, which is what
  \"Mathlib pinned to the installed toolchain\" means."
fi

# ---- the Kruskal probe (plan.md's named toolchain risk for 2E.3) ----------------------------------
if [ "${1:-}" = "--probe-kruskal" ]; then
  echo
  echo "LEAN: probing the pinned Mathlib for the whistle's well-quasi-order theorems (2E.3)."
  echo "      This is a REPORT, not a gate: plan.md requires the answer BEFORE 2E.3 starts, and the"
  echo "      fallback if Kruskal is absent is to prove it from Higman."
  MATHLIB=$LEAN_DIR/.lake/packages/mathlib
  [ -d "$MATHLIB" ] || fail "Mathlib is not fetched: run \`lake update\` in proofs/lean"
  echo
  echo "  --- HIGMAN'S LEMMA (the fallback's premise) ---"
  grep -rn --include='*.lean' "Higman's Lemma" "$MATHLIB/Mathlib" 2>/dev/null \
    | sed 's|^.*/Mathlib/|    Mathlib/|' | head -4
  grep -rn --include='*.lean' "partiallyWellOrderedOn_sublistForall" "$MATHLIB/Mathlib" 2>/dev/null \
    | sed 's|^.*/Mathlib/|    Mathlib/|' | head -4
  echo
  echo "  --- KRUSKAL'S TREE THEOREM (what T3 admits) ---"
  echo "      NOTE: \`Kruskal\` in Mathlib is KRUSKAL-KATONA (a shadow/set-family theorem), which is"
  echo "      a DIFFERENT result and does not bear on the whistle.  Files matching \`Kruskal\`:"
  grep -rl --include='*.lean' "Kruskal" "$MATHLIB/Mathlib" 2>/dev/null \
    | sed 's|^.*/Mathlib/|    Mathlib/|'
  echo "      A tree-embedding well-quasi-order would be named for \`SubtreeEmbedding\` /"
  echo "      \`treeEmbedding\` / Nash-Williams' minimal-bad-sequence argument; searching for those:"
  for pat in SubtreeEmbedding treeEmbedding minimalBad "minimal bad"; do
    n=$(grep -rl --include='*.lean' "$pat" "$MATHLIB/Mathlib" 2>/dev/null | wc -l | tr -d ' ')
    printf '        %-20s %s file(s)\n' "$pat" "$n"
  done
  echo
  echo "  --- WELL-QUASI-ORDER VOCABULARY (what 2E.3 builds the WQO in) ---"
  grep -rn --include='*.lean' "^theorem .*WellQuasiOrder\|^def WellQuasiOrder\|^ *WellQuasiOrdered" \
    "$MATHLIB/Mathlib/Order/WellFoundedSet.lean" 2>/dev/null \
    | sed 's|^|    |' | head -6
  exit 0
fi

# ---- 3. the build --------------------------------------------------------------------------------
echo
echo "LEAN: lake build in proofs/lean"
BUILD_LOG=$(mktemp "${TMPDIR:-/tmp}/checklean.XXXXXX") || exit 1
trap 'rm -f "$BUILD_LOG" "$ROOT/target/lean-mechanized.tsv.tmp" "$LEAN_DIR/.axioms_probe.lean"' EXIT INT TERM HUP
if ! (cd "$LEAN_DIR" && "$LAKE_BIN" build) > "$BUILD_LOG" 2>&1; then
  sed 's/^/  /' "$BUILD_LOG" | grep -v '^  trace:' | tail -40
  fail "lake build did not succeed (full log above)"
fi
grep -v '^trace:' "$BUILD_LOG" | tail -3 | sed 's/^/  /'

# A `sorry` anywhere is reported by the build as a WARNING, and a warning does not change the exit
# status.  Step 5 catches it per marked theorem through `#print axioms`, which is the authoritative
# check; this is the cheap tree-wide one, and it is here so an UNMARKED `sorry` is visible too.
if grep -q "declaration uses 'sorry'" "$BUILD_LOG"; then
  grep -n "declaration uses 'sorry'" "$BUILD_LOG" | head -10 | sed 's/^/  /'
  fail "the package builds but a declaration uses \`sorry\`.  A sorried theorem compiles and proves
  nothing, and the status tables would go on reporting the claim it is supposed to carry."
fi

# ---- 4/5. the markers and their axioms -----------------------------------------------------------
echo
echo "LEAN: resolving \`% MECHANIZED-IN:\` markers"
# ==WHERE A MARKER MAY LIVE, AND WHY THE SCAN IS THIS NARROW==
# A marker's job is to sit in an OBLIGATION FILE of the proof corpora, as a TPTP `%` comment or an
# SMT `;` comment.  The scan is deliberately restricted to that, because a wider one reads PROSE
# ABOUT the marker as a marker -- twice, measured:
#
#   * `proofs/lean/Zippy/Pointwise.lean`'s own header quotes the syntax, and an early scan came back with
#     a lone backtick as a "malformed marker";
#   * `docs/TRUSTED.md`'s specification table contains the literal
#     `| `% MECHANIZED-IN: <file>#<thm>` | ...`, and the next scan came back with the PLACEHOLDER
#     `<file>#<thm>` and failed the gate on a marker nobody wrote.
#
# Three guards, each closing one of those:
#   1. only `proofs` and `terminating`, only `.p`/`.smt2`, and never under `proofs/lean` (the
#      marker's TARGET is not a carrier).  `docs/` is out: a claim about a status row belongs in the
#      file whose status it is, not in prose.
#   2. ANCHORED AT LINE START (`^[[:space:]]*[;%]`).  A real marker is a comment LINE; the two
#      false positives were both mid-line, inside quoted prose.
#   3. the token may not contain `<`, `>`, backtick or `|` -- the characters a placeholder or a
#      markdown table cell is made of -- and must contain exactly one `#`.
MARKERS=$(find proofs terminating -type f \
            \( -name '*.p' -o -name '*.smt2' \) \
            -not -path 'proofs/lean/*' -print0 2>/dev/null \
          | xargs -0 grep -hoE '^[[:space:]]*[;%][[:space:]]*MECHANIZED-IN:[[:space:]]*[^[:space:]`<>|]+#[^[:space:]`<>|]+' 2>/dev/null \
          | sed 's|.*MECHANIZED-IN:[[:space:]]*||' | sort -u)
# ENTRY-LEVEL MARKERS (2E.6): docs/TRUSTED.md names, per entry, the Lean theorem that IS the entry's
# schema, on a line of its own beginning `MECHANIZED-IN:` (no comment sigil -- it is markdown).
# `scripts/proof_closure.py` lifts every row reaching that entry when the theorem is witnessed here.
ENTRY_MARKERS=$(grep -hoE '^MECHANIZED-IN:[[:space:]]*[^[:space:]`<>|]+#[^[:space:]`<>|]+' docs/TRUSTED.md 2>/dev/null \
                | sed 's|^MECHANIZED-IN:[[:space:]]*||' | sort -u)
MARKERS=$(printf '%s\n%s\n' "$MARKERS" "$ENTRY_MARKERS" | grep -v '^$' | sort -u)
if [ -z "$MARKERS" ]; then
  echo "  none yet (plan.md 1E.3 attaches the first ones; 0.5 only makes the marker MEAN something)."
  echo "  The marker Zippy/Pointwise.lean documents is checked below as the self-test."
  MARKERS="proofs/lean/Zippy/Pointwise.lean#Zippy.Space.unwrap_wrap"
  SELFTEST=1
else
  SELFTEST=0
fi

axioms_of() {   # $1 = fully qualified theorem name -> prints the axiom list, or "UNRESOLVED"
  cat > "$LEAN_DIR/.axioms_probe.lean" <<EOF
import Zippy
#print axioms $1
EOF
  out=$( (cd "$LEAN_DIR" && env LEAN_PATH="$("$LAKE_BIN" env printenv LEAN_PATH 2>/dev/null)" \
            "$LAKE_BIN" env lean .axioms_probe.lean) 2>&1 )
  rm -f "$LEAN_DIR/.axioms_probe.lean"
  printf '%s' "$out"
}

# THE WITNESS.  `scripts/proof_closure.py` lifts a status row from `PROVED-MODULO T1` to unqualified
# `PROVED` only for a marker THIS SCRIPT has resolved, and it learns that from this table rather than
# by re-running the Lean build itself.  It lives under `target/` and is NOT committed, deliberately:
# it records what the LOCAL toolchain checked, so a reader who has not run the gate gets no lift at
# all instead of inheriting someone else's build.  Written atomically, for 0.1's reason.
WITNESS=$ROOT/target/lean-mechanized.tsv
mkdir -p "$ROOT/target"
: > "$WITNESS.tmp"

rc=0
for m in $MARKERS; do
  file=${m%%#*}
  thm=${m#*#}
  if [ "$file" = "$m" ] || [ -z "$thm" ]; then
    echo "  BAD MARKER  $m  (expected <lean file>#<fully qualified theorem>)"; rc=1; continue
  fi
  if [ ! -f "$ROOT/$file" ]; then
    echo "  MISSING     $m  ($file does not exist)"; rc=1; continue
  fi
  out=$(axioms_of "$thm")
  case "$out" in
    *"'$thm' depends on axioms"*|*"'$thm' does not depend on any axioms"*)
      ax=$(printf '%s' "$out" | sed -n "s/.*depends on axioms: //p")
      [ -z "$ax" ] && ax="(none)"
      case "$ax" in
        *sorryAx*)
          echo "  SORRIED     $m  axioms: $ax"; rc=1 ;;
        *)
          echo "  OK          $m"
          echo "              axioms: $ax"
          printf '%s\t%s\t%s\t%s\n' "$m" "$thm" "$ax" "MECHANIZED" >> "$WITNESS.tmp" ;;
      esac ;;
    *)
      echo "  UNRESOLVED  $m"
      printf '%s\n' "$out" | grep -v '^ *$' | head -4 | sed 's/^/              /'
      rc=1 ;;
  esac
done

# Publish the witness only when EVERY marker resolved: a partial witness would let one good marker
# lift a row while a broken one in the same corpus went unreported.
if [ "$rc" -eq 0 ]; then
  mv "$WITNESS.tmp" "$WITNESS"
  echo "  witness: target/lean-mechanized.tsv ($(wc -l < "$WITNESS" | tr -d ' ') resolved marker(s))"
else
  rm -f "$WITNESS.tmp" "$WITNESS"
fi

[ "$rc" -eq 0 ] || fail "one or more \`% MECHANIZED-IN:\` markers do not resolve to a proved theorem.
  A marker is what lifts a status table row from PROVED-MODULO to unqualified PROVED, so an
  unresolved one would lift a claim on the strength of a typo."

# ---- 6. THE AXIOM AUDIT OVER EVERY THEOREM, not only the marked ones -------------------------------
#
# 2E.6's requirement is that this script "lists the axioms each theorem uses and they are exactly
# Lean's".  A marked theorem gets that above; an UNMARKED one is the more dangerous case, because a
# theorem nothing points at is exactly where a `sorry` or a stray `axiom` survives unnoticed.  So the
# list is derived FROM THE SOURCE — every top-level `theorem` in `proofs/lean/Zippy` — rather than
# maintained by hand, and a new theorem is audited the moment it is written.
#
# `Classical.choice` is ALLOWED and named: Mathlib's `Finset`/`Set` development is classical, so a
# theorem stated over them may legitimately use it.  `sorryAx` is not, and neither is any axiom whose
# name is not one of Lean's four.
echo
echo "LEAN: axiom audit over every theorem in the package"
# THE LIST COMES FROM THE ELABORATED ENVIRONMENT, NOT FROM A GREP OVER THE SOURCE.  A previous
# revision derived it with `grep '^theorem NAME'` and prefixed `Zippy.`; measured (2026-09-04), 22 of
# its 56 names did not resolve: a doc-comment line beginning with the word "theorem", the dotted
# `Space.unwrap_wrap` truncated at the dot, and every theorem in the `Zippy.Kleene` / `Zippy.Counting`
# namespaces probed under the wrong prefix.  A `#print axioms` on a name that does not exist is an
# `unknown constant`, so the audit could not pass -- and an audit that cannot pass is not gating.
# `run_cmd` below walks the environment for every THEOREM whose name is under `Zippy`, so a new
# theorem in a new namespace is audited the moment it elaborates, with the name Lean gave it.
cat > "$LEAN_DIR/.axioms_probe.lean" <<'PROBE'
import Zippy
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    -- skip the equation lemmas Lean generates for every definition (`f.eq_1`, `f.eq_def`): they
    -- are not theorems anyone wrote, and their axioms are those of `f`'s own well-founded/structural
    -- recursion compilation, which the audit of `f`'s consumers already sees.
    let isEqn := match n with
      | .str _ s => s.startsWith "eq_"
      | _ => false
    if (`Zippy).isPrefixOf n && !n.isInternal && !isEqn then
      match ci with
      | .thmInfo _ => names := names.push n
      | _ => pure ()
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  for n in sorted do
    let axs ← collectAxioms n
    let axsSorted := axs.qsort (fun a b => a.toString < b.toString)
    if axsSorted.isEmpty then
      IO.println s!"AXIOMS {n} : (none)"
    else
      IO.println s!"AXIOMS {n} : {String.intercalate ", " (axsSorted.toList.map toString)}"
PROBE
AXOUT=$( (cd "$LEAN_DIR" && "$LAKE_BIN" env lean .axioms_probe.lean) 2>&1 )
rm -f "$LEAN_DIR/.axioms_probe.lean"
AXLINES=$(printf '%s\n' "$AXOUT" | grep '^AXIOMS ' || true)
NTHM=$(printf '%s\n' "$AXLINES" | grep -c . || true)
[ "$NTHM" -gt 0 ] || { printf '%s\n' "$AXOUT" | head -20 | sed 's/^/    /';
                       fail "the axiom audit enumerated no theorem under \`Zippy\` -- the probe did not run"; }
# Every axiom name the audit saw, deduplicated.
SEEN=$(printf '%s\n' "$AXLINES" | sed -n 's/^AXIOMS [^:]*: //p' | grep -v '^(none)$' \
       | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u)
NAXFREE=$(printf '%s\n' "$AXLINES" | grep -c ': (none)$' || true)
echo "  $NTHM theorem(s) audited; $NAXFREE depend on NO axiom at all"
echo "  axioms used across the package: $(printf '%s\n' "$SEEN" | tr '\n' ' ')"
# The per-theorem list, which is what 2E.6's gate sentence asks this script to print.
printf '%s\n' "$AXLINES" | sed 's/^AXIOMS /    /'
if printf '%s\n' "$SEEN" | grep -q 'sorryAx'; then
  printf '%s\n' "$AXOUT" | grep -B0 'sorryAx' | head -10 | sed 's/^/    /'
  fail "a theorem depends on \`sorryAx\`: it compiles and proves nothing."
fi
UNEXPECTED=$(printf '%s\n' "$SEEN" \
             | grep -vxE 'propext|Quot.sound|Classical.choice|Lean.ofReduceBool|Lean.ofReduceNat' || true)
if [ -n "$UNEXPECTED" ]; then
  echo "  UNEXPECTED: $(printf '%s\n' "$UNEXPECTED" | tr '\n' ' ')"
  fail "the package depends on an axiom that is not one of Lean's own.  2E.6 requires the axiom set
  of every PROVED claim to be exactly Lean's; an extra axiom here is a trusted assumption with no
  entry in docs/TRUSTED.md."
fi
if printf '%s\n' "$AXOUT" | grep -qE "^[^ ]*\.lean:[0-9]+:[0-9]+: error"; then
  printf '%s\n' "$AXOUT" | grep -E ": error" | head -5 | sed 's/^/    /'
  fail "the axiom-audit probe itself failed to elaborate; see the errors above."
fi

echo
if [ "$SELFTEST" = "1" ]; then
  echo "LEAN GATE OK: the package builds, no \`sorry\`, and the marker mechanism resolves (self-test)."
else
  echo "LEAN GATE OK: the package builds, no \`sorry\`, and every \`% MECHANIZED-IN:\` marker resolves."
fi
exit 0
