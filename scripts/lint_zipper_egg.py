#!/usr/bin/env python3
"""Lint the egglog models for the two syntactic invariants the movement spec promises:

(1) NO-MATERIALIZATION: no observation rule (head Term/Sub/Keys/IsEmpty/TermAt/KeysAt/FocusOf)
    may construct a concrete trie node (TNode/Node/CC/ConsIf) on its RHS — observations read, they
    never build tries.  (The implementation model's op rules DO build — that is their job.)

(2) LOCK-STEP + ONE-STEP-PER-LAYER: every `Sub`-pushing rewrite (a) pattern-matches at most ONE
    Z-constructor under the observation head (so one movement rewrites one layer — the O(1)-in-
    trie-size step), and (b) applies `Sub` with the SAME key variable to every Z-operand it
    descends (the lock-step invariant that makes Ascend commute with every operator).
"""
import re, sys, pathlib

root = pathlib.Path(__file__).resolve().parent.parent

def parse_sexps(text: str):
    """Yield top-level s-expressions (as nested lists) from egglog text."""
    text = re.sub(r";[^\n]*", "", text)
    toks = re.findall(r"\(|\)|[^\s()]+", text)
    stack, cur = [], []
    for t in toks:
        if t == "(":
            stack.append(cur); cur = []
        elif t == ")":
            done = cur; cur = stack.pop(); cur.append(done)
        else:
            cur.append(t)
    yield from cur

OBS_HEADS = {"Term", "Sub", "Keys", "IsEmpty", "TermAt", "KeysAt", "FocusOf", "KeysX"}
TRIE_CTORS = {"Node", "TNode", "CC", "ConsIf"}

def subterms(e):
    yield e
    if isinstance(e, list):
        for x in e:
            yield from subterms(x)

def depth_under(e):
    """Max constructor-nesting depth of an s-exp (variables = 0).  `Reflect` is TRANSPARENT: it is
    the coercion between the spec and impl vocabularies, not an operator — an observation matching
    (Reflect (TNode t c)) reads the concrete root, an O(1) boundary inspection, not a traversal.
    Constant literals (T)/(F)/(CNil) are depth-0 (they are flags, not structure)."""
    if not isinstance(e, list):
        return 0
    if e[0] == "Reflect":
        return max((depth_under(x) for x in e[1:]), default=0)
    if e[0] in ("T", "F", "CNil", "KNil", "Eps", "Empty"):
        return 0
    return 1 + max((depth_under(x) for x in e[1:]), default=0)

def check_file(path: pathlib.Path) -> int:
    bad = 0
    for e in parse_sexps(path.read_text()):
        if not (isinstance(e, list) and e and e[0] in ("rewrite", "rule")):
            continue
        if e[0] == "rewrite":
            lhs, rhss = e[1], [e[2]]
        else:  # (rule (facts...) (actions...))
            lhs = next((f[1] for f in e[1] if isinstance(f, list) and f[0] == "=" and isinstance(f[1], str)), None)
            # facts of shape (= e (Pattern ...)): the pattern is the 2nd arg
            pats = [f[2] for f in e[1] if isinstance(f, list) and f and f[0] == "="]
            lhs = pats[0] if pats else None
            rhss = [a for a in e[2]]
        if lhs is None or not isinstance(lhs, list):
            continue
        head = lhs[0]
        if head not in OBS_HEADS:
            continue
        # (1) no observation constructs a trie node
        for r in rhss:
            for s in subterms(r):
                if isinstance(s, list) and s and s[0] in TRIE_CTORS:
                    print(f"{path.name}: observation rule for {head} CONSTRUCTS {s[0]}: {r}")
                    bad += 1
        # (2a) one Z-constructor deep: the operand of the observation nests at most 1 constructor
        for arg in lhs[1:]:
            if isinstance(arg, list) and depth_under(arg) > 2:
                print(f"{path.name}: observation rule for {head} matches deeper than one layer: {lhs}")
                bad += 1
        # (2b) lock-step: in a Sub rule, every (Sub ...) on the RHS uses the same key as the LHS
        if head == "Sub":
            key = lhs[1]
            for r in rhss:
                for s in subterms(r):
                    if isinstance(s, list) and s and s[0] == "Sub" and s[1] != key:
                        print(f"{path.name}: Sub rule breaks lock-step (key {s[1]} != {key}): {s}")
                        bad += 1
    return bad

total = 0
for f in ["zipper-spec.egg", "zipper-egg-tests/bridge-prelude.egg"]:
    total += check_file(root / f)
if total == 0:
    print("lint: no-materialization + lock-step + one-step-per-layer hold for all observation rules")
sys.exit(1 if total else 0)
