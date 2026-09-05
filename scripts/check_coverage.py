#!/usr/bin/env python3
"""STRUCTURAL COVERAGE (tasks.md D1): every claimed feature occurs inside a checked end-to-end chain.

`proofs/pipeline/COVERAGE.tsv` is written by `EquivPipelineTest` from the PARSED source AST and the typed
proof-trace DAGs (tasks.md C3), one row per (cornerstone, kind, feature):

    cornerstone  kind  feature  artifact  artifact-node  trace  trace-node  claim  state

  kind          constructor | binder | call | recursion | law | resource | boundary | hole
  artifact-node T:<digest>     a term of the trace's term table containing the feature's constructor
                law:<name>     the cell artifact's `; laws used:` / `; STEP` header names the law
                BOUNDARY:<b>   the cell artifact's `; BOUNDARY: <b>` header
                HOLE:#holeN    the zipper artifact's `;   #holeN = <Ctor>` hole line
                RULE:<id>      a row of proofs/spatial/REGISTRY.tsv
  trace-node    N:<id>         a node of the trace DAG whose kind (and law / endpoint term) matches the row
  claim         <cornerstone>/<boundary>/<form>   the CLAIMS.tsv cell whose trace closure discharges it
  state         covered | exercised-unproved | proved-unexercised | unsupported

Census rows (cornerstone `*`, trace/trace-node/claim `census`) record the two states no cornerstone
produces: a language constructor no cornerstone exercises (`unsupported`) and a certified law no
cornerstone's trace fires (`proved-unexercised`).  Every constructor of the language and every registry
law must appear in exactly one of the two places.

This script re-derives every row from the files alone — no Scala.  An empty item, an unattached string
(a node or term that does not exist or does not carry the feature), a claim whose closure is OPEN but is
marked covered, or a missing census entry is an error.  `--selftest` mutates copies (blank a feature,
delete the referenced trace node, delete the referenced term, misname a law, open a closure) and
requires each mutation to be caught.

    python3 scripts/check_coverage.py [--root DIR] [--selftest]
"""
import os, re, shutil, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KINDS = {"constructor", "binder", "call", "recursion", "law", "resource", "boundary", "hole"}
STATES = {"covered", "exercised-unproved", "proved-unexercised", "unsupported"}
SPACE_CTORS = ["Empty", "Call", "Mention", "Singleton", "Literal", "Union", "Intersection", "Subtraction", "Restriction",
               "Raffination", "Composition", "Iteration", "Fixpoint", "Fold", "Wrap", "Unwrap", "TailsUnion",
               "TailsIntersection", "GroundedPS", "GroundedSS", "Range"]
PATH_CTORS = ["Deref", "Constant", "Concat", "GroundedPP", "GroundedSP"]
ALL_CTORS = SPACE_CTORS + PATH_CTORS
BINDERS = {"Iteration", "Fixpoint", "Fold"}
RECURSION_KINDS = {"Unfold", "Fold", "Generalization"}
BOUNDARY_KINDS = {"BackendRefinement", "GraphOptimizerNoOp", "Compose", "OptimizerNoOp", "AlphaEquivalence"}


def rows(path):
    out = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            out.append(line.split("\t"))
    return out


def parse_trace(path):
    """node id -> (kind, before, after, fields, deps); digest -> term"""
    nodes, terms = {}, {}
    root = -1
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("# root\t"):
                root = int(line.split("\t")[1]); continue
            if not line.strip() or line.startswith("#"):
                continue
            cols = line.split("\t")
            if cols[0] == "T" and len(cols) >= 3:
                terms[cols[1]] = cols[2]
            elif len(cols) >= 6 and cols[0].isdigit():
                nodes[int(cols[0])] = (cols[1], cols[2], cols[3], cols[4], cols[5])
    nodes["root"] = root
    return nodes, terms


def term_has(term, kind, feature):
    if kind == "call":
        return f'Call("{feature}"' in term
    if feature == "Empty":
        return re.search(r'(?<![A-Za-z0-9_"])Empty(?![A-Za-z0-9_(])', term) is not None
    return re.search(r'(?<![A-Za-z0-9_"])' + re.escape(feature) + r'\(', term) is not None


def check(root):
    problems = []
    cov = os.path.join(root, "proofs", "pipeline", "COVERAGE.tsv")
    claims_f = os.path.join(root, "proofs", "pipeline", "CLAIMS.tsv")
    closure_f = os.path.join(root, "target", "trace-closure.tsv")
    laws_f = os.path.join(root, "proofs", "laws", "REGISTRY.tsv")
    for f in (cov, claims_f, laws_f):
        if not os.path.exists(f):
            return [f"missing {os.path.relpath(f, root)}"]
    if not os.path.exists(closure_f):
        return ["target/trace-closure.tsv is missing: run `python3 scripts/proof_closure.py --check` first (the closure is what discharges a claim)"]
    claims = {}
    for c in rows(claims_f):
        if len(c) >= 3:
            claims[(c[0], c[1], c[2])] = c
    closure = {c[0]: c[1] for c in rows(closure_f) if len(c) >= 2}
    laws = {c[0].strip() for c in rows(laws_f) if len(c) >= 2}
    trace_cache = {}

    def trace(rel):
        if rel not in trace_cache:
            p = os.path.join(root, rel)
            trace_cache[rel] = parse_trace(p) if os.path.exists(p) else None
        return trace_cache[rel]

    art_cache = {}

    def artifact_text(rel):
        if rel not in art_cache:
            p = os.path.join(root, rel)
            art_cache[rel] = open(p, encoding="utf-8", errors="replace").read() if os.path.exists(p) else None
        return art_cache[rel]

    exercised_ctors, exercised_laws = set(), set()
    census_ctors, census_laws = set(), set()
    by_cell_kinds = {}
    n = 0
    for cols in rows(cov):
        n += 1
        if len(cols) != 9:
            problems.append(f"row {n}: {len(cols)} columns, not 9: {cols[:3]}")
            continue
        stone, kind, feature, artifact, anode, tr, tnode, claim, state = [c.strip() for c in cols]
        tag = f"{stone}/{kind}/{feature}"
        if any(not c or c == "-" for c in cols):
            problems.append(f"{tag}: an empty item"); continue
        if kind not in KINDS:
            problems.append(f"{tag}: unknown kind"); continue
        if state not in STATES:
            problems.append(f"{tag}: unknown state `{state}`"); continue
        # ---- census rows
        if stone == "*":
            if (artifact, anode, tr, tnode, claim) != ("census", "census", "census", "census", "census"):
                problems.append(f"{tag}: a census row must say `census` in artifact, artifact-node, trace, trace-node and claim"); continue
            if kind == "constructor" and state == "unsupported":
                if feature not in ALL_CTORS:
                    problems.append(f"{tag}: not a constructor of the language")
                census_ctors.add(feature)
            elif kind == "law" and state == "proved-unexercised":
                if feature not in laws:
                    problems.append(f"{tag}: not a registry law")
                census_laws.add(feature)
            else:
                problems.append(f"{tag}: a census row is `constructor/unsupported` or `law/proved-unexercised`")
            continue
        if state in ("unsupported", "proved-unexercised"):
            problems.append(f"{tag}: state `{state}` is a census state, but the row names cornerstone {stone}"); continue
        # ---- the artifact and its node
        text = artifact_text(artifact)
        if text is None:
            problems.append(f"{tag}: artifact {artifact} does not exist"); continue
        tdata = trace(tr)
        if tdata is None:
            problems.append(f"{tag}: trace {tr} does not exist"); continue
        nodes, terms = tdata
        tdigest = None
        if anode.startswith("T:"):
            tdigest = anode[2:]
            if artifact != tr:
                problems.append(f"{tag}: a T: node must name the trace as its artifact ({artifact} != {tr})")
            if tdigest not in terms:
                problems.append(f"{tag}: term {tdigest} is not in the term table of {tr}"); continue
            if kind not in ("constructor", "binder", "call", "hole", "recursion"):
                problems.append(f"{tag}: a T: node is for constructor/binder/call/hole/recursion rows"); continue
            if kind != "recursion" and not term_has(terms[tdigest], kind, feature):
                problems.append(f"{tag}: term {tdigest} does not contain `{feature}`"); continue
        elif anode.startswith("law:"):
            name = anode[4:]
            if kind != "law" or name != feature:
                problems.append(f"{tag}: a law: node names its own law"); continue
            lines = [l for l in text.splitlines() if l.startswith(";") and ("law" in l or "STEP" in l or "rule" in l)]
            if not any(re.search(r'(?<![A-Za-z0-9_-])' + re.escape(name) + r'(?![A-Za-z0-9_-])', l) for l in lines):
                problems.append(f"{tag}: {artifact} names no law `{name}` in its law/STEP headers"); continue
        elif anode.startswith("BOUNDARY:"):
            b = anode[len("BOUNDARY:"):]
            if kind != "boundary" or b != feature:
                problems.append(f"{tag}: a BOUNDARY: node names its own boundary"); continue
            if not re.search(r'^;\s*BOUNDARY:\s*' + re.escape(b) + r'\s*$', text, re.M):
                problems.append(f"{tag}: {artifact} has no `; BOUNDARY: {b}` header"); continue
        elif anode.startswith("HOLE:"):
            hole = anode[5:]
            if kind != "hole":
                problems.append(f"{tag}: a HOLE: node is for hole rows"); continue
            if not re.search(r'^;\s*' + re.escape(hole) + r'\s*=\s*' + re.escape(feature) + r'\s*$', text, re.M):
                problems.append(f"{tag}: {artifact} has no hole line `{hole} = {feature}`"); continue
        elif anode.startswith("RULE:"):
            rid = anode[5:]
            if kind != "resource" or rid != feature:
                problems.append(f"{tag}: a RULE: node names its own rule"); continue
            if not any(c[0].strip() == rid for c in rows(os.path.join(root, artifact)) if c):
                problems.append(f"{tag}: {artifact} has no rule {rid}"); continue
        else:
            problems.append(f"{tag}: unknown artifact-node form `{anode}`"); continue
        # ---- the trace node
        if not tnode.startswith("N:") or not tnode[2:].isdigit():
            problems.append(f"{tag}: trace-node `{tnode}` is not N:<id>"); continue
        nid = int(tnode[2:])
        if nid not in nodes:
            problems.append(f"{tag}: node {nid} is not in {tr}"); continue
        nkind, before, after, fields, _deps = nodes[nid]
        if kind == "law":
            if nkind != "LawInstance" or f"law={feature};" not in fields + ";":
                problems.append(f"{tag}: node {nid} is {nkind} [{fields[:40]}], not a LawInstance of `{feature}`"); continue
        elif kind == "recursion":
            if feature not in RECURSION_KINDS or nkind != feature:
                problems.append(f"{tag}: node {nid} is {nkind}, not `{feature}`"); continue
            if tdigest is not None and tdigest not in (before, after):
                problems.append(f"{tag}: node {nid} does not carry term {tdigest}"); continue
        elif kind == "boundary":
            if nkind not in BOUNDARY_KINDS and nid != nodes.get("root"):
                problems.append(f"{tag}: node {nid} is {nkind}, neither a boundary node nor the trace root"); continue
        elif kind == "hole":
            if nkind not in BOUNDARY_KINDS and tdigest is None:
                problems.append(f"{tag}: a hole row's node is a boundary node or carries the hole's term"); continue
            if tdigest is not None and tdigest not in (before, after):
                problems.append(f"{tag}: node {nid} does not carry term {tdigest}"); continue
        elif kind == "resource":
            # a resource rule is discharged by proofs/spatial/STATUS.tsv, not by the trace: a row marked covered
            # must name a rule whose status is not OPEN
            stf = os.path.join(root, "proofs", "spatial", "STATUS.tsv")
            verdict = next((c[-1].strip() for c in rows(stf) if c and c[0].strip() == feature), None) if os.path.exists(stf) else None
            if verdict is None:
                problems.append(f"{tag}: proofs/spatial/STATUS.tsv has no verdict for rule {feature}"); continue
            if verdict == "OPEN" and state == "covered":
                problems.append(f"{tag}: rule {feature} is OPEN but the row says covered"); continue
        else:  # constructor / binder / call
            if tdigest is None or tdigest not in (before, after):
                problems.append(f"{tag}: node {nid} ({nkind} {before}->{after}) does not carry term {tdigest}"); continue
        # ---- the claim and its closure
        parts = claim.split("/")
        if len(parts) != 3 or (parts[0], parts[1], parts[2]) not in claims:
            problems.append(f"{tag}: claim `{claim}` is not a CLAIMS.tsv cell"); continue
        cst, cb, cform = parts
        cell = f"{cst}-{cb}" + ("-agnostic" if cform == "agnostic" else "")
        if cell not in closure:
            problems.append(f"{tag}: no trace-closure row for cell {cell}"); continue
        expected = "covered" if closure[cell] != "OPEN" else "exercised-unproved"
        if state != expected:
            problems.append(f"{tag}: state `{state}` but the closure of {cell} is {closure[cell]} (expected `{expected}`)"); continue
        if kind in ("constructor", "binder", "hole"):
            exercised_ctors.add(feature)
        if kind == "law":
            exercised_laws.add(feature)
        by_cell_kinds.setdefault(stone, set()).add(kind)
    # ---- completeness: every cornerstone, every constructor, every law is accounted for exactly once
    stones = {c[0] for c in claims}
    for st in sorted(stones):
        for need in ("constructor", "boundary"):
            if need not in by_cell_kinds.get(st, set()):
                problems.append(f"cornerstone {st}: no `{need}` row")
    for c in ALL_CTORS:
        ex, ce = c in exercised_ctors, c in census_ctors
        if not ex and not ce:
            problems.append(f"constructor {c}: neither exercised by a cornerstone nor listed `unsupported`")
        if ex and ce:
            problems.append(f"constructor {c}: exercised AND listed `unsupported`")
    for l in sorted(laws):
        ex, ce = l in exercised_laws, l in census_laws
        if not ex and not ce:
            problems.append(f"law {l}: neither fired in a cornerstone trace nor listed `proved-unexercised`")
        if ex and ce:
            problems.append(f"law {l}: fired AND listed `proved-unexercised`")
    return problems


def summary(root):
    cov = os.path.join(root, "proofs", "pipeline", "COVERAGE.tsv")
    states = {}
    for c in rows(cov):
        if len(c) == 9:
            states[c[8]] = states.get(c[8], 0) + 1
    return states


def selftest():
    """copy what the checker reads into a temp root, mutate, require a failure"""
    src_rows = rows(os.path.join(ROOT, "proofs", "pipeline", "COVERAGE.tsv"))
    real = [r for r in src_rows if len(r) == 9 and r[0] != "*"]
    if not real:
        return ["selftest: no cornerstone rows to mutate"]

    def make_root():
        tmp = tempfile.mkdtemp(prefix="coverage-selftest-")
        for rel in ("proofs/pipeline/COVERAGE.tsv", "proofs/pipeline/CLAIMS.tsv", "proofs/laws/REGISTRY.tsv",
                    "proofs/spatial/REGISTRY.tsv", "proofs/spatial/STATUS.tsv", "target/trace-closure.tsv"):
            d = os.path.join(tmp, os.path.dirname(rel)); os.makedirs(d, exist_ok=True)
            shutil.copy(os.path.join(ROOT, rel), os.path.join(tmp, rel))
        for rel in sorted({r[3] for r in real} | {r[5] for r in real}):
            d = os.path.join(tmp, os.path.dirname(rel)); os.makedirs(d, exist_ok=True)
            shutil.copy(os.path.join(ROOT, rel), os.path.join(tmp, rel))
        return tmp

    def write_cov(tmp, rs):
        with open(os.path.join(tmp, "proofs", "pipeline", "COVERAGE.tsv"), "w", encoding="utf-8") as f:
            for r in rs:
                f.write("\t".join(r) + "\n")

    failures = []
    base = make_root()
    if check(base):
        return ["selftest: the unmutated copy does not pass: " + "; ".join(check(base)[:3])]
    shutil.rmtree(base)
    law_row = next((r for r in real if r[1] == "law"), None)
    ctor_row = next((r for r in real if r[1] in ("constructor", "binder") and r[4].startswith("T:")), None)
    mutations = []
    # 1. an empty feature
    def m1(tmp):
        rs = [list(r) for r in src_rows]; rs[[i for i, r in enumerate(rs) if r == real[0]][0]][2] = ""; write_cov(tmp, rs)
    mutations.append(("blank feature", m1))
    # 2. the referenced trace node deleted
    if law_row:
        def m2(tmp, law_row=law_row):
            p = os.path.join(tmp, law_row[5]); nid = law_row[6][2:]
            lines = open(p, encoding="utf-8").read().splitlines(True)
            open(p, "w", encoding="utf-8").writelines(l for l in lines if not l.startswith(nid + "\t"))
        mutations.append(("deleted trace node", m2))
        # 4. a law the artifact does not name
        def m4(tmp, law_row=law_row):
            rs = [list(r) for r in src_rows]; i = [i for i, r in enumerate(rs) if r == law_row][0]
            rs[i][2] = "no-such-law"; rs[i][4] = "law:no-such-law"; write_cov(tmp, rs)
        mutations.append(("misnamed law", m4))
    # 3. the referenced term deleted
    if ctor_row:
        def m3(tmp, ctor_row=ctor_row):
            p = os.path.join(tmp, ctor_row[5]); d = ctor_row[4][2:]
            lines = open(p, encoding="utf-8").read().splitlines(True)
            open(p, "w", encoding="utf-8").writelines(l for l in lines if not l.startswith("T\t" + d + "\t"))
        mutations.append(("deleted term", m3))
    # 5. a claim's closure opened while the row says covered
    def m5(tmp):
        r = next(r for r in real if r[8] == "covered")
        st, b, form = r[7].split("/"); cell = f"{st}-{b}" + ("-agnostic" if form == "agnostic" else "")
        p = os.path.join(tmp, "target", "trace-closure.tsv")
        lines = open(p, encoding="utf-8").read().splitlines(True)
        out = []
        for l in lines:
            c = l.rstrip("\n").split("\t")
            if c and c[0] == cell:
                c[1] = "OPEN"; l = "\t".join(c) + "\n"
            out.append(l)
        open(p, "w", encoding="utf-8").writelines(out)
    mutations.append(("opened closure", m5))
    for name, mut in mutations:
        tmp = make_root()
        mut(tmp)
        ps = check(tmp)
        if not ps:
            failures.append(f"selftest: mutation `{name}` was NOT caught")
        else:
            print(f"  selftest `{name}`: caught ({ps[0][:90]})")
        shutil.rmtree(tmp)
    return failures


def main(argv):
    root = ROOT
    if "--root" in argv:
        root = argv[argv.index("--root") + 1]
    if "--selftest" in argv:
        fs = selftest()
        for f in fs:
            print(f"  !! {f}")
        print(f"coverage selftest: {'OK' if not fs else str(len(fs)) + ' failure(s)'}")
        return 1 if fs else 0
    ps = check(root)
    for p in ps:
        print(f"  !! {p}")
    st = summary(root)
    print("coverage: " + ", ".join(f"{k}={v}" for k, v in sorted(st.items())) + f"; {len(ps)} problem(s)")
    return 1 if ps else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
