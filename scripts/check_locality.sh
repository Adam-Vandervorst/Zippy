#!/bin/sh
# Locality as a CHECKED property (not a comment), two mechanized halves:
#
# (1) WORK BOUND: a chain of d descents over an OPAQUE source (Src) saturates to an e-graph whose
#     ChildOf table has EXACTLY d entries — linear in d and, because Src is opaque, provably
#     independent of any trie's size or contents (there is nothing else the rules could read).
#     Checked here for d = 1..8 and for a 2-operand virtual cursor (2d lookups).
#
# (2) ONE-STEP-PER-LAYER: every observation rule rewrites only the top constructor (LHS pattern
#     depth <= 1 Z-constructor under the observation head) — a syntactic property of the rule set,
#     enforced by scripts/lint_zipper_egg.py (run from here too).
set -e
cd "$(dirname "$0")/.."
EGG=~/.cargo/bin/egglog
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

awk '/SCOPE 1 /{exit} {print}' zipper-spec.egg > "$TMP/prelude.egg"

fail=0
for d in 1 2 3 4 5 6 7 8; do
  { cat "$TMP/prelude.egg"
    term="(Src (N 1))"; i=1
    while [ $i -le $d ]; do term="(Sub $i $term)"; i=$((i+1)); done
    echo "(let \$chain $term)"
    echo "(run 40)"
    echo "(print-size ChildOf)"
  } > "$TMP/chain$d.egg"
  got=$("$EGG" "$TMP/chain$d.egg" 2>/dev/null | tail -1)
  if [ "$got" = "$d" ]; then echo "d=$d descents over an opaque source: ChildOf = $got  OK (== d)"
  else echo "d=$d: ChildOf = $got EXPECTED $d  FAIL"; fail=1; fi
done

# a 2-operand virtual cursor: d descents cost exactly 2d child lookups (one per operand per layer)
for d in 3 6; do
  { cat "$TMP/prelude.egg"
    term="(Union (Src (N 1)) (Src (N 2)))"; i=1
    while [ $i -le $d ]; do term="(Sub $i $term)"; i=$((i+1)); done
    echo "(let \$chain $term)"
    echo "(run 40)"
    echo "(print-size ChildOf)"
  } > "$TMP/union$d.egg"
  got=$("$EGG" "$TMP/union$d.egg" 2>/dev/null | tail -1)
  want=$((2*d))
  if [ "$got" = "$want" ]; then echo "d=$d descents through a virtual ∪: ChildOf = $got  OK (== 2d)"
  else echo "d=$d ∪: ChildOf = $got EXPECTED $want  FAIL"; fail=1; fi
done

python3 scripts/lint_zipper_egg.py || fail=1
exit $fail
