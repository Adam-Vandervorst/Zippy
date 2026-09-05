#!/usr/bin/env python3
"""THE INDEPENDENT STRUCTURAL CHECK OF THE TYPED PROOF TRACES.

`morkl.ProofTrace.Checker` REPLAYS a trace in Scala (re-applies each law, re-runs each substitution,
re-checks each instance).  This script is the second, independent reader of the same artifacts: it
parses every `proofs/pipeline/traces/*.trace.tsv` written by `EquivPipelineTest` and checks what a
proof DAG must satisfy REGARDLESS of what the steps mean:

  * it is a DAG: every dependency is an earlier node id, the root exists;
  * it COMPOSES: in a `Compose`, each step's `after` digest is the next step's `before` digest and the
    node's endpoints are the chain's; a `Positional`'s justifying node exists; a `Generalization`'s
    skeleton and hole traces exist;
  * its LEAVES are what a claim may rest on: a `LawInstance` whose law has a row in
    proofs/laws/REGISTRY.tsv and a non-empty matcher; an `Unfold`/`Fold`/`AlphaEquivalence`
    (definitional — O6a/O12b, Lean); a `BackendRefinement` whose artifact EXISTS and carries a goal
    (an `(assert (not`, a `(check`, or a LAW-JUSTIFIED chain) — a marker-only artifact is refused;
    an `OptimizerNoOp`;
  * an IDENTITY claim (root before == after) carries both an `AlphaEquivalence` and an `OptimizerNoOp`
    unless it rests on real steps;
  * every declared pipeline cell (proofs/pipeline/CLAIMS.tsv) has a trace file, and every trace
    file names a declared cell.

Exit 1 on any failure.  Nothing here trusts a marker: a claim that is only a comment is a failure.
"""
import pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TRACES = ROOT / "proofs/pipeline/traces"
LEAF_KINDS = {"LawInstance", "AlphaEquivalence", "Unfold", "Fold", "BackendRefinement", "OptimizerNoOp", "GraphOptimizerNoOp"}
INNER_KINDS = {"Positional", "Compose", "Generalization"}

def law_registry():
    f = ROOT / "proofs/laws/REGISTRY.tsv"
    out = set()
    for line in f.read_text().splitlines():
        if not line.strip() or line.startswith("#") or line.startswith("law\t"):
            continue
        out.add(line.split("\t")[0])
    return out

def parse(path):
    nodes, terms, root = [], {}, None
    for line in path.read_text().splitlines():
        if line.startswith("# root\t"):
            root = int(line.split("\t")[1]); continue
        if not line.strip() or line.startswith("#"):
            continue
        cols = line.split("\t")
        if cols[0] == "T":
            terms[cols[1]] = cols[2] if len(cols) > 2 else ""
            continue
        nid, kind, before, after, fields, deps = cols[:6]
        fd = {}
        if fields != "-":
            for kv in fields.split(";"):
                if "=" in kv:
                    k, v = kv.split("=", 1); fd[k] = v
        dep = [] if deps == "-" else [int(d) for d in deps.split(",") if d]
        nodes.append(dict(id=int(nid), kind=kind, before=before, after=after, fields=fd, deps=dep))
    return nodes, terms, root

def artifact_ok(rel):
    f = ROOT / rel
    if not f.is_file():
        return f"artifact {rel} does not exist"
    text = f.read_text(errors="replace")
    has_goal = "(assert (not" in text or "(check " in text or "LAW-JUSTIFIED-NO-RESIDUAL" in text or "LAW-JUSTIFIED:" in text
    marker = any(m in text for m in ("TRIVIAL-NO-OBLIGATION", "IDENTICAL-STRUCTURE", "IDENTICAL-LITERAL", "SINGLE-SIDE-OBSERVATION"))
    if marker and not has_goal:
        return f"artifact {rel} is a marker, not an obligation"
    if not has_goal:
        return f"artifact {rel} carries no goal"
    return None

def check_file(path, laws, problems):
    nodes, terms, root = parse(path)
    name = path.name
    if root is None or not nodes:
        problems.append(f"{name}: no root or no nodes"); return
    if root >= len(nodes):
        problems.append(f"{name}: root {root} is not a node"); return
    by_id = {n["id"]: n for n in nodes}
    for n in nodes:
        for d in n["deps"]:
            if d not in by_id:
                problems.append(f"{name} node {n['id']}: dependency {d} is not a node")
            elif d >= n["id"]:
                problems.append(f"{name} node {n['id']}: dependency {d} is not earlier — not a DAG")
        for h in (n["before"], n["after"]):
            if h not in terms:
                problems.append(f"{name} node {n['id']}: endpoint digest {h} has no term")
        k = n["kind"]
        if k not in LEAF_KINDS | INNER_KINDS:
            problems.append(f"{name} node {n['id']}: unknown kind {k}")
        if k == "LawInstance":
            law = n["fields"].get("law", "")
            if law not in laws:
                problems.append(f"{name} node {n['id']}: law `{law}` has no registry row")
            if not n["fields"].get("changed"):
                problems.append(f"{name} node {n['id']}: a law instance with no matcher positions")
        if k == "BackendRefinement":
            err = artifact_ok(n["fields"].get("artifact", ""))
            if err: problems.append(f"{name} node {n['id']}: {err}")
            if not n["fields"].get("obligation"):
                problems.append(f"{name} node {n['id']}: no obligation id")
        if k == "Compose":
            steps = [int(s) for s in n["fields"].get("steps", "").split(",") if s]
            if not steps:
                problems.append(f"{name} node {n['id']}: empty composition"); continue
            if steps[0] in by_id and by_id[steps[0]]["before"] != n["before"]:
                problems.append(f"{name} node {n['id']}: composition does not start at its `before`")
            if steps[-1] in by_id and by_id[steps[-1]]["after"] != n["after"]:
                problems.append(f"{name} node {n['id']}: composition does not end at its `after`")
            for a, b in zip(steps, steps[1:]):
                if a in by_id and b in by_id and by_id[a]["after"] != by_id[b]["before"]:
                    problems.append(f"{name} node {n['id']}: steps {a} and {b} do not compose")
        if k == "Positional":
            by = int(n["fields"].get("by", "-1"))
            if by not in by_id: problems.append(f"{name} node {n['id']}: justifying node {by} missing")
        if k == "Generalization":
            st = int(n["fields"].get("skeletonTrace", "-1"))
            if st not in by_id: problems.append(f"{name} node {n['id']}: skeleton trace {st} missing")
            for h in n["fields"].get("holes", "").split(","):
                if h and int(h.split(":")[3]) not in by_id:
                    problems.append(f"{name} node {n['id']}: hole trace missing")
    r = by_id[root]
    reach, stack = set(), [root]
    while stack:
        i = stack.pop()
        if i in reach: continue
        reach.add(i); stack.extend(by_id[i]["deps"] if i in by_id else [])
    kinds = {by_id[i]["kind"] for i in reach if i in by_id}
    if r["before"] == r["after"]:
        real = kinds & {"LawInstance", "Unfold", "Fold", "Generalization", "BackendRefinement"}
        if not real and not ("AlphaEquivalence" in kinds and ({"OptimizerNoOp", "GraphOptimizerNoOp"} & kinds)):
            problems.append(f"{name}: an identity claim without both an alpha-equivalence and a verified optimiser no-op")
    if not (kinds & LEAF_KINDS):
        problems.append(f"{name}: no leaf of a permitted kind reachable from the root")
    return kinds

def main():
    problems = []
    laws = law_registry()
    if not TRACES.is_dir():
        print("no proofs/pipeline/traces directory: run `sbt \"testOnly morkl.EquivPipelineTest\"`"); return 1
    files = sorted(TRACES.glob("*.trace.tsv"))
    summary = {}
    for f in files:
        kinds = check_file(f, laws, problems) or set()
        summary[f.name] = ",".join(sorted(kinds))
    # every declared cell has a trace
    claims = ROOT / "proofs/pipeline/CLAIMS.tsv"
    declared = []
    if claims.is_file():
        for line in claims.read_text().splitlines():
            if not line.strip() or line.startswith("#"): continue
            cols = line.split("\t")
            paths = [c.strip() for c in cols if "/" in c and c.strip().endswith((".smt2", ".egg"))]
            if paths:
                declared.append(paths[0])   # the artifact column (position varies: a verdict column may follow)
    have = {f.name.removesuffix(".trace.tsv") for f in files}
    for cell in declared:
        stem = pathlib.Path(cell).name.rsplit(".", 1)[0]
        if stem not in have:
            problems.append(f"declared cell {cell} has no trace file")
    for f in files:
        stem = f.name.removesuffix(".trace.tsv")
        if not any(pathlib.Path(c).name.rsplit(".", 1)[0] == stem for c in declared):
            problems.append(f"trace {f.name} names no declared cell")
    for k, v in sorted(summary.items()):
        print(f"  {k:48s} {v}")
    print(f"traces: {len(files)} files, {len(declared)} declared cells, {len(problems)} problem(s)")
    for p in problems[:40]: print("  !! " + p)
    return 1 if problems else 0

if __name__ == "__main__":
    sys.exit(main())
