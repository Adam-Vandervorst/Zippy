#!/usr/bin/env python3
"""ASSERT-LEVEL CLOSURE FOR THE SMT TIERS.

WHY THIS EXISTS.  `scripts/proof_closure.py` computes what each reported `PROVED` rests on by following
`include(...)` edges -- which SMT-LIB does not have.  An SMT obligation carries its axioms INLINE as
top-level `(assert ...)` forms, and the trusted base was invisible there: measured on 2026-09-04,
the six SMT corpora hold 1686 top-level asserts, of which 39 are structural-induction SCHEMA
instances (the SMT twin of docs/TRUSTED.md T1) asserted with no marker and no entry, plus a handful
of assumed facts (`fixpoint_is_lfp.smt2`'s monotone/inflationary premises, `gsem_join_union_sound`'s
measure facts, `mutual_tagged_bekic`'s projection facts) that `proof_closure.py` could not see.  So
an SMT row could read unqualified `PROVED` while resting on an induction principle first-order logic
cannot state -- the exact defect the closure exists to report.

WHAT THIS SCRIPT DOES.  For every `.smt2` under the six SMT corpora it parses the top-level forms and
classifies EVERY `(assert ...)` as exactly one of:

  GOAL         the negated theorem: `(assert (not ...))`, or the assert immediately before a
               `(check-sat)` (the generators' "premises ∧ ¬conclusion" shape), or one inside a
               `(push)`/`(pop)` block that ends in `(check-sat)`.
  STONE        an in-file stepping stone: the formula was first checked as a goal inside a
               `(push) (assert (not F)) (check-sat) (pop)` block earlier in the same file and is
               then re-asserted (`terminating/`'s discipline: "base, step, then the principle").
               Only the RE-ASSERTION of a checked formula counts; the trigger annotation `(! F
               :pattern ...)` is stripped before comparing.
  DEFINITION   a characterisation of a symbol DECLARED IN THIS FILE: `(forall V (= (f x..) rhs))`,
               `(= (f c..) rhs)`, `(forall V (f x..))`, `(forall V (not (f x..)))`, where the
               arguments of the head are bound variables, constructor patterns or numerals.  The
               shared `append`/`isPrefix` prelude every generator emits is exactly this shape.
  DERIVED      an explicitly marked in-corpus lemma: a comment naming the obligation file(s) it is
               certified in -- the three phrasings the generators already use (`certified lemmas
               assumed below: A, B`, `assumed: A (...)`, `assumed, certified in <corpus>: A, B`) and
               the canonical `; DERIVED-FROM: A[, B]`.  Each named file must have a `PROVED*` row
               in a status table (or be a Lean theorem `proofs/lean/...#Name` that exists).
  ASSUMED      an explicitly marked trusted assumption: `; ASSUMED: T<n>` naming an entry of
               docs/TRUSTED.md, or `; PREMISE: <text>` for a hypothesis of the conditional theorem
               the file states (e.g. `fixpoint_is_lfp.smt2` assumes monotonicity of `F`; its verdict
               is for the conditional statement and the discharging obligation is named in the text).
  UNCLASSIFIED anything else -- and that FAILS the check.

A marker comment applies to the asserts that follow it, one per named file for DERIVED, until the
next non-assert command; a marker on the same line as an assert applies to that assert only.

OUTPUT.  A per-corpus census, the list of UNCLASSIFIED asserts, and `target/assert-closure.tsv`:
one row per obligation file with the TRANSITIVE set of trusted entries it rests on (its own ASSUMED
markers plus those of every file it is DERIVED from), which `scripts/proof_closure.py` reads to
qualify SMT verdicts the way `include` closures qualify TPTP verdicts.

    python3 scripts/check_asserts.py            report + write the closure table; exit 1 on any
                                                UNCLASSIFIED assert or dangling DERIVED reference
    python3 scripts/check_asserts.py --verbose  also list every assert with its class
"""

import argparse, collections, os, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TARGET = ROOT / "target" / "assert-closure.tsv"

# the six SMT corpora and the status table that reports each
CORPORA = [
    ("proofs",                       ROOT / "proofs",                        "proofs/STATUS.tsv",          ""),
    ("proofs/laws",                  ROOT / "proofs/laws",                   "proofs/STATUS.tsv",          "laws/"),
    ("proofs/spatial",               ROOT / "proofs/spatial",                "proofs/STATUS.tsv",          "spatial/"),
    ("proofs/spatial-semantic",      ROOT / "proofs/spatial-semantic",       "proofs/spatial-semantic/STATUS.tsv", ""),
    ("proofs/pipeline",              ROOT / "proofs/pipeline",               "proofs/pipeline/STATUS.tsv", ""),
    ("proofs/pipeline/fixpoint-gate", ROOT / "proofs/pipeline/fixpoint-gate", "proofs/pipeline/fixpoint-gate/STATUS.tsv", ""),
    ("terminating",                  ROOT / "terminating",                   "terminating/STATUS.tsv",     ""),
]

# ---------------------------------------------------------------------------------------------
# an S-expression reader that keeps comments
# ---------------------------------------------------------------------------------------------

class Form:
    __slots__ = ("sexp", "line", "comments", "inline_comment", "text")
    def __init__(self, sexp, line, comments, inline_comment, text):
        self.sexp, self.line, self.comments, self.inline_comment, self.text = sexp, line, comments, inline_comment, text

def read_forms(text):
    """top-level forms with the comment lines immediately above each (contiguous, no blank line)"""
    forms = []
    i, n, line = 0, len(text), 1
    pending_comments = []
    last_was_blank = False
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1; i += 1
            # a blank line breaks the comment block
            j = i
            while j < n and text[j] in " \t": j += 1
            if j < n and text[j] == "\n":
                pending_comments = []
            continue
        if c in " \t\r":
            i += 1; continue
        if c == ";":
            j = text.find("\n", i)
            if j < 0: j = n
            pending_comments.append(text[i:j])
            i = j; continue
        if c == "(":
            start, start_line = i, line
            depth, j = 0, i
            in_str = None
            while j < n:
                ch = text[j]
                if in_str:
                    if ch == in_str: in_str = None
                    elif ch == "\n": line += 1
                elif ch in '"|':
                    in_str = ch
                elif ch == ";":
                    k = text.find("\n", j)
                    j = (k if k >= 0 else n) - 1
                elif ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        break
                elif ch == "\n":
                    line += 1
                j += 1
            raw = text[start:j + 1]
            # an inline comment on the same line after the form
            k = text.find("\n", j + 1)
            rest = text[j + 1:(k if k >= 0 else n)]
            inline = rest.strip() if rest.strip().startswith(";") else ""
            forms.append(Form(parse(raw), start_line, pending_comments, inline, raw))
            pending_comments = []
            i = j + 1
            continue
        # a stray token
        i += 1
    return forms

def parse(s):
    toks = re.findall(r'\(|\)|"(?:[^"]|"")*"|\|[^|]*\||[^\s()]+', s)
    pos = 0
    def rd():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t == "(":
            out = []
            while toks[pos] != ")":
                out.append(rd())
            pos += 1
            return out
        return t
    return rd()

def strip_annot(e):
    """drop `(! F :pattern ...)` / `:named` annotations, recursively"""
    if isinstance(e, list):
        if e and e[0] == "!" and len(e) >= 2:
            return strip_annot(e[1])
        return [strip_annot(x) for x in e]
    return e

def head(e):
    return e[0] if isinstance(e, list) and e else e

def render(e):
    return "(" + " ".join(render(x) for x in e) + ")" if isinstance(e, list) else str(e)

# ---------------------------------------------------------------------------------------------
# classification
# ---------------------------------------------------------------------------------------------

MARK_ASSUMED = re.compile(r";\s*ASSUMED:\s*(T\d+)\b")
MARK_PREMISE = re.compile(r";\s*PREMISE:\s*(.+)")
MARK_DEF = re.compile(r";\s*DEFINITION\b")
MARK_STONE = re.compile(r";\s*STONE\b")
MARK_GOAL = re.compile(r";\s*GOAL\b")
MARK_DERIVED = re.compile(r";\s*DERIVED-FROM:\s*(.+)")
# the three pre-existing phrasings
MARK_CERT_BELOW = re.compile(r";\s*certified lemmas assumed below:\s*(.+)")
MARK_ASSUMED_FILE = re.compile(r";\s*assumed:\s*(\S+\.smt2)")
MARK_ASSUMED_CORPUS = re.compile(r";\s*assumed, certified in (this corpus|[^:]+):\s*(.+)")

def files_in(txt):
    """the .smt2 / .lean#thm references in a marker's payload"""
    out = []
    for tok in re.split(r"[,\s]+", txt.strip()):
        tok = tok.strip("().;")
        if not tok: continue
        if tok.endswith(".smt2") or ".lean#" in tok:
            out.append(tok)
    return out

def is_var_or_pattern(e, bound, ctors, consts):
    """a bound variable, a numeral, a constructor pattern over such, or a declared constant"""
    if isinstance(e, str):
        return (e in bound or e in ctors or e in consts or e in ("true", "false")
                or re.fullmatch(r"-?\d+(\.\d+)?|#b[01]+|#x[0-9a-fA-F]+", e) is not None)
    if isinstance(e, list) and e:
        h = e[0]
        if h in ctors or h in ("-", "+", "_"):
            return all(is_var_or_pattern(x, bound, ctors, consts) for x in e[1:])
        if h == "as":
            return True
        return False
    return False

def bound_vars(binders):
    out = set()
    for b in binders:
        if isinstance(b, list) and b:
            out.add(b[0])
    return out

def is_definition(body, declared, ctors, consts):
    """`(forall V (= (f x..) rhs))`, `(= (f c..) rhs)`, `(forall V (f x..))`, `(forall V (not (f x..)))`,
    where `f` is declared in the file and its arguments are variables, constructor patterns, declared
    constants, or ONE level of another declared symbol applied to such (an OBSERVER applied to the
    operation being characterised: `(term (union a b))`, `(mem x (setminus a b))`, `(getk (fkcons j v r) k)`)."""
    e = strip_annot(body)
    bound = set()
    while isinstance(e, list) and e and e[0] == "forall":
        bound |= bound_vars(e[1]); e = e[2]
    def nested_ok(a):
        return (isinstance(a, list) and a and isinstance(a[0], str) and a[0] in declared
                and all(is_var_or_pattern(x, bound, ctors, consts) for x in a[1:]))
    def app_ok(app, nested):
        """`f` declared, arguments patterns, with at most `nested` observer-style nested applications"""
        if not (isinstance(app, list) and app and isinstance(app[0], str) and app[0] in declared):
            return False
        n = 0
        for a in app[1:]:
            if is_var_or_pattern(a, bound, ctors, consts): continue
            if nested_ok(a): n += 1; continue
            return False
        return n <= nested
    def eqn_ok(x):
        if isinstance(x, list) and x:
            # an EQUATION defines its head: `(= (f pat..) rhs)`, or an observer on one nested
            # operation `(= (mem x (setminus a b)) rhs)`; a PREDICATE form must be on patterns only,
            # so `(subset (C n) (C (+ n 1)))` -- a THEOREM about C -- is not a definition
            if x[0] == "=" and len(x) == 3 and (app_ok(x[1], 1) or app_ok(x[2], 1)):
                return True
            if x[0] == "not" and len(x) == 2 and app_ok(x[1], 1):
                return True
            if app_ok(x, 0):
                return True
        return False
    if eqn_ok(e):
        return True
    # a GUARDED equation `(=> guard (= (f pat..) rhs))` -- a recurrence with a side condition
    # (`(>= k 0)`, `(< k1 k2)`, `(isEmp v)`), or a conjunction of equations
    if isinstance(e, list) and e and e[0] == "=>" and len(e) == 3 and eqn_ok(e[2]):
        return True
    if isinstance(e, list) and e and e[0] == "and" and all(eqn_ok(x) for x in e[1:]):
        return True
    # EXTENSIONALITY of a set sort: `(=> (forall (x) (= (mem x a) (mem x b))) (= a b))`
    if (isinstance(e, list) and len(e) == 3 and e[0] == "=>" and isinstance(e[1], list) and e[1]
            and e[1][0] == "forall" and isinstance(e[1][2], list) and e[1][2] and e[1][2][0] == "="
            and isinstance(e[2], list) and e[2] and e[2][0] == "="
            and isinstance(e[1][2][1], list) and e[1][2][1] and e[1][2][1][0] in declared):
        return True
    return False

# THE TWO APPEND LEMMAS EVERY PRELUDE RE-ASSERTS.  `gen_law_obligations.py` marks them with
# `; certified lemmas assumed below: ...`; the hand-written files under proofs/ and the Scala emitter
# `AgSmt` state the same two formulas without the comment.  Recognised by formula, so a copy without
# the comment is still classified -- and still checked against the two certifying files' verdicts.
KNOWN_LEMMAS = {
    render(parse("(forall ((k2 Int) (p Path) (q Path) (r Path)) (= (= (cons k2 p) (append q r)) "
                 "(or (and (= q nil) (= r (cons k2 p))) (exists ((q2 Path)) (and (= q (cons k2 q2)) (= p (append q2 r)))))))")):
        "proofs/lemma_append_cons.smt2",
    render(parse("(forall ((q Path)) (= (append q nil) q))")): "proofs/lemma_append_nil.smt2",
}

def classify_file(path, verbose=False):
    text = path.read_text()
    forms = read_forms(text)
    declared, ctors, consts = set(), {"nil", "cons"}, set()
    for f in forms:
        if isinstance(f.sexp, list) and f.sexp and f.sexp[0] in ("declare-fun", "declare-const"):
            declared.add(f.sexp[1])
            if f.sexp[0] == "declare-const" or (len(f.sexp) > 2 and f.sexp[2] == []):
                consts.add(f.sexp[1])
        if isinstance(f.sexp, list) and f.sexp and f.sexp[0] == "declare-datatypes":
            # ((T 0) ...) (((c1 ...) (c2 ...)) ...)
            for dt in f.sexp[2]:
                for c in dt:
                    ctors.add(c[0] if isinstance(c, list) else c)
        if isinstance(f.sexp, list) and f.sexp and f.sexp[0] in ("define-fun", "define-fun-rec"):
            declared.add(f.sexp[1])
    # goals checked inside push/pop blocks, for the STONE rule
    checked = []           # normalised formulas F for which `(assert (not F))` was checked
    results = []           # (Form, kind, detail)
    depth = 0
    pending_derived = []   # queue of file references from a marker above
    # pre-scan: which assert indices are immediately followed by (check-sat) (ignoring comments)
    follow_check = set()
    for idx, f in enumerate(forms):
        if idx + 1 < len(forms) and head(forms[idx + 1].sexp) == "check-sat":
            follow_check.add(idx)
    for idx, f in enumerate(forms):
        h = head(f.sexp)
        if h == "push":
            depth += 1; continue
        if h == "pop":
            depth -= 1; continue
        if h != "assert":
            if h not in ("check-sat",):
                pending_derived = []   # a declaration or definition ends a marker's scope
            continue
        body = f.sexp[1]
        norm = render(strip_annot(body))
        kind, detail = None, ""
        comments = f.comments + ([f.inline_comment] if f.inline_comment else [])
        # ---- explicit markers first ----
        for c in comments:
            m = MARK_ASSUMED.search(c)
            if m: kind, detail = "ASSUMED", m.group(1); break
            m = MARK_PREMISE.search(c)
            if m: kind, detail = "ASSUMED", "PREMISE: " + m.group(1).strip(); break
            if MARK_DEF.search(c): kind, detail = "DEFINITION", "marked"; break
            if MARK_STONE.search(c): kind, detail = "STONE", "marked"; break
            if MARK_GOAL.search(c): kind, detail = "GOAL", "marked"; break
            m = MARK_DERIVED.search(c) or MARK_CERT_BELOW.search(c)
            if m:
                pending_derived = files_in(m.group(1)); break
            m = MARK_ASSUMED_FILE.search(c)
            if m:
                pending_derived = [m.group(1)]; break
            m = MARK_ASSUMED_CORPUS.search(c)
            if m:
                where = m.group(1).strip()
                refs = files_in(m.group(2))
                if where != "this corpus":
                    refs = [os.path.join(where.rstrip("/"), r) if "/" not in r else r for r in refs]
                pending_derived = refs; break
        if kind is None and pending_derived:
            kind, detail = "DERIVED", pending_derived.pop(0)
        # ---- goals ----
        if kind is None:
            if isinstance(body, list) and body and body[0] == "not":
                kind, detail = "GOAL", "negated"
            elif idx in follow_check:
                kind, detail = "GOAL", "before check-sat"
            elif depth > 0:
                kind, detail = "GOAL", "inside push/pop"
        # ---- the two prelude lemmas, by formula ----
        if kind is None and norm in KNOWN_LEMMAS and not path.name.startswith("lemma_append"):
            kind, detail = "DERIVED", KNOWN_LEMMAS[norm]
        # ---- stepping stones ----
        if kind is None and norm in checked:
            kind, detail = "STONE", "checked above"
        # ---- definitions ----
        if kind is None and is_definition(body, declared, ctors, consts):
            kind, detail = "DEFINITION", "characterises " + str(defined_head(body))
        if kind is None:
            kind = "UNCLASSIFIED"
            if is_induction_schema(body):
                detail = ("INDUCTION-SCHEMA SHAPE `(=> (and base step) (forall ...))` — a datatype schema "
                          "is `; ASSUMED: T1`, a chain-index one `; ASSUMED: T8`, a Park instance is "
                          "`; DERIVED-FROM: <the fixpoint theorem>` (emitted by AgSmt.emitParkInstances)")
        # record the negated goal's formula for later re-assertion
        if isinstance(body, list) and body and body[0] == "not":
            checked.append(render(strip_annot(body[1])))
        results.append((f, kind, detail))
    return results

def is_induction_schema(body):
    """`(=> (and BASE STEP) (forall (x) (P x)))` — the datatype induction axiom instantiated at `P`"""
    e = strip_annot(body)
    return (isinstance(e, list) and len(e) == 3 and e[0] == "=>" and isinstance(e[1], list) and e[1]
            and e[1][0] == "and" and isinstance(e[2], list) and e[2] and e[2][0] == "forall")

def defined_head(body):
    e = strip_annot(body)
    while isinstance(e, list) and e and e[0] == "forall":
        e = e[2]
    if isinstance(e, list) and e:
        if e[0] in ("=", "not") and isinstance(e[1], list): return e[1][0]
        return e[0]
    return e

# ---------------------------------------------------------------------------------------------
# status lookup and the closure table
# ---------------------------------------------------------------------------------------------

def read_status_tables():
    """every reported verdict, keyed by several spellings of the file name"""
    verdicts = {}
    tables = [
        (ROOT / "proofs/STATUS.tsv", ""),
        (ROOT / "proofs/spatial-semantic/STATUS.tsv", "proofs/spatial-semantic/"),
        (ROOT / "proofs/pipeline/STATUS.tsv", "proofs/pipeline/"),
        (ROOT / "proofs/pipeline/fixpoint-gate/STATUS.tsv", "proofs/pipeline/fixpoint-gate/"),
        (ROOT / "terminating/STATUS.tsv", "terminating/"),
    ]
    for t, prefix in tables:
        if not t.exists(): continue
        for line in t.read_text().splitlines():
            if not line.strip() or line.startswith("#") or line.startswith("file\t"): continue
            cols = line.split("\t")
            name, verdict = cols[0], cols[-1]
            base = name[:-5] if name.endswith(".smt2") else name
            keys = {base, base + ".smt2", prefix + base, prefix + base + ".smt2"}
            if t.name == "STATUS.tsv" and prefix == "":
                keys |= {"proofs/" + base, "proofs/" + base + ".smt2"}
            for k in keys:
                verdicts[k] = verdict
    return verdicts

def lean_theorem_exists(ref):
    file, thm = ref.split("#", 1)
    p = ROOT / file
    if not p.exists(): return False
    short = thm.rsplit(".", 1)[-1]
    return re.search(r"\b(theorem|lemma)\s+" + re.escape(short) + r"\b", p.read_text()) is not None or \
           re.search(r"\b(theorem|lemma)\s+\S*\." + re.escape(short) + r"\b", p.read_text()) is not None

def resolve_ref(ref, corpus_dir):
    """the repo-relative path a DERIVED reference names, or None"""
    if ".lean#" in ref:
        return ref if lean_theorem_exists(ref) else None
    cands = [corpus_dir / ref, ROOT / ref, ROOT / "proofs" / ref]
    for c in cands:
        if c.exists():
            return str(c.resolve().relative_to(ROOT))
    return None

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verbose", action="store_true")
    a = ap.parse_args()
    verdicts = read_status_tables()
    trusted_ids = set(re.findall(r"^## (T\d+)\.", (ROOT / "docs/TRUSTED.md").read_text(), re.M))
    problems = []
    census = collections.OrderedDict()
    own_assumed = {}       # repo-relative file -> set of T ids
    derived_from = {}      # repo-relative file -> set of repo-relative files / lean refs
    total = 0
    for label, d, _status, _prefix in CORPORA:
        counts = collections.Counter()
        for path in sorted(d.glob("*.smt2")):
            rel = str(path.relative_to(ROOT))
            res = classify_file(path)
            own_assumed.setdefault(rel, set()); derived_from.setdefault(rel, set())
            for f, kind, detail in res:
                total += 1
                counts[kind] += 1
                if a.verbose:
                    print(f"  {rel}:{f.line}: {kind:12s} {detail}")
                if kind == "UNCLASSIFIED":
                    problems.append(f"{rel}:{f.line}: UNCLASSIFIED assert  {f.text[:110].replace(chr(10), ' ')}" +
                                    (f"   <- {detail}" if detail else ""))
                elif kind == "ASSUMED":
                    if detail.startswith("PREMISE:"):
                        pass
                    elif detail not in trusted_ids:
                        problems.append(f"{rel}:{f.line}: ASSUMED names `{detail}`, which is not an entry of docs/TRUSTED.md")
                    else:
                        own_assumed[rel].add(detail)
                elif kind == "DERIVED":
                    target = resolve_ref(detail, d)
                    if target is None:
                        problems.append(f"{rel}:{f.line}: DERIVED-FROM `{detail}` does not resolve to a file or Lean theorem")
                    elif ".lean#" not in target:
                        v = verdicts.get(target) or verdicts.get(target.removesuffix(".smt2"))
                        if v is None:
                            problems.append(f"{rel}:{f.line}: DERIVED-FROM `{target}` has no row in any status table")
                        elif not v.startswith("PROVED"):
                            problems.append(f"{rel}:{f.line}: DERIVED-FROM `{target}` is reported `{v}`, not PROVED")
                        derived_from[rel].add(target)
                    else:
                        derived_from[rel].add(target)
        census[label] = counts
    # ---- the transitive closure ----
    closure = {}
    def close(f, seen):
        if f in closure: return closure[f]
        if f in seen: return set()
        seen.add(f)
        acc = set(own_assumed.get(f, set()))
        for g in derived_from.get(f, set()):
            if ".lean#" in g: continue
            acc |= close(g, seen)
        closure[f] = acc
        return acc
    for f in own_assumed:
        close(f, set())
    # ---- report ----
    print("assert-level closure over the SMT tiers")
    kinds = ["GOAL", "STONE", "DEFINITION", "DERIVED", "ASSUMED", "UNCLASSIFIED"]
    print(f"  {'corpus':32s} " + " ".join(f"{k:>12s}" for k in kinds))
    for label, counts in census.items():
        print(f"  {label:32s} " + " ".join(f"{counts.get(k, 0):12d}" for k in kinds))
    print(f"  {total} top-level asserts classified")
    by_t = collections.Counter()
    for f, ts in closure.items():
        for t in ts: by_t[t] += 1
    if by_t:
        print("  files whose closure reaches a trusted entry: " +
              ", ".join(f"{t}: {n}" for t, n in sorted(by_t.items())))
    TARGET.parent.mkdir(parents=True, exist_ok=True)
    tmp = TARGET.with_suffix(".tsv.tmp")
    with tmp.open("w") as out:
        out.write("# file\ttrusted-entries (transitive, via DERIVED-FROM)\n")
        for f in sorted(closure):
            out.write(f"{f}\t{','.join(sorted(closure[f])) or '-'}\n")
    tmp.replace(TARGET)
    print(f"  closure table written: {TARGET.relative_to(ROOT)}")
    if problems:
        print(f"\n{len(problems)} PROBLEM(S):")
        for p in problems[:200]:
            print("  " + p)
        if len(problems) > 200:
            print(f"  ... and {len(problems) - 200} more")
        sys.exit(1)
    print("assert closure: OK")

if __name__ == "__main__":
    main()
