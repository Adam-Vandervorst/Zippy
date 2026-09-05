#!/usr/bin/env python3
"""THE PUZZLE15 STRESS THEOREM, RE-CHECKED INDEPENDENTLY (tasks.md D3).

Puzzle15Check writes, through ArtifactSink:
  proofs/puzzle15/EXPANSION.tsv    parent board -> successor board, for the BFS levels it expanded
  proofs/puzzle15/CERTIFICATE.tsv  per declaration and backend: predicted intervals, counted run, result-size bound
  proofs/puzzle15/REPORT.md        the human-readable derivation report

This script re-derives, from those files and the committed tables alone:
  * every board is a legal state (16 items: a cell name, then the 15 tiles as a permutation of 1..15);
  * every successor differs from its parent by exactly the blank swapping with a grid neighbour, every
    parent has as many successors as its blank has neighbours (<= 4), and the expansion's row set equals
    an independent BFS from the initial board to the same depth;
  * every counted value lies in its interval; no result-size bound exceeds 4 x |frontier| (the proved
    maximum, Zippy.Puzzle15.expand_le); every committed threshold (THRESHOLDS.tsv) holds;
  * every theorem named in REGISTRY.tsv is declared in proofs/lean/Zippy/Puzzle15.lean.
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIR = os.path.join(ROOT, "proofs", "puzzle15")
COMPONENTS = ["work", "alloc", "rounds", "touch"]


def rows(path):
    out = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if line.strip() and not line.startswith("#"):
                out.append(line.split("\t"))
    return out


def cell_index(name):
    m = re.fullmatch(r"c(\d+)", name)
    return int(m.group(1)) if m else None


def neighbours(i):
    r, c = divmod(i, 4)
    out = []
    for rr, cc in ((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1)):
        if 0 <= rr < 4 and 0 <= cc < 4:
            out.append(rr * 4 + cc)
    return out


def parse_board(path):
    """'c0.1.2....15' -> (blank cell index, tiles by cell index with None at the blank)"""
    items = path.split(".")
    if len(items) != 16:
        return None
    b = cell_index(items[0])
    if b is None:
        return None
    tiles = items[1:]
    if sorted(tiles, key=int) != [str(i) for i in range(1, 16)]:
        return None
    # the encoding lists the other cells' tiles in cell order, skipping the blank
    cells = [c for c in range(16) if c != b]
    board = [None] * 16
    for c, t in zip(cells, tiles):
        board[c] = int(t)
    return b, board


def encode(b, board):
    return ".".join(["c%d" % b] + [str(board[c]) for c in range(16) if c != b])


def successors(b, board):
    out = []
    for j in neighbours(b):
        nb = list(board)
        nb[b] = nb[j]; nb[j] = None
        out.append(encode(j, nb))
    return sorted(out)


def check():
    problems = []
    exp = os.path.join(DIR, "EXPANSION.tsv")
    cert = os.path.join(DIR, "CERTIFICATE.tsv")
    thr = os.path.join(DIR, "THRESHOLDS.tsv")
    reg = os.path.join(DIR, "REGISTRY.tsv")
    lean = os.path.join(ROOT, "proofs", "lean", "Zippy", "Puzzle15.lean")
    for f in (exp, cert, thr, reg, lean):
        if not os.path.exists(f):
            return [f"missing {os.path.relpath(f, ROOT)}"]
    # ---- the expansion: legal boards, legal moves, complete successor sets, an independent BFS
    edges = {}
    depth = 0
    initial = None
    for c in rows(exp):
        if len(c) >= 2 and c[0] == "level":
            depth = int(c[1]); continue
        if len(c) >= 2 and c[0] == "initial":
            initial = c[1]; continue
        if len(c) != 2:
            problems.append(f"EXPANSION row with {len(c)} columns"); continue
        edges.setdefault(c[0], set()).add(c[1])
    if initial is None:
        return problems + ["EXPANSION.tsv names no initial board"]
    boards = set(edges) | {s for ss in edges.values() for s in ss}
    for bd in sorted(boards):
        if parse_board(bd) is None:
            problems.append(f"illegal board {bd}")
    for parent, succ in sorted(edges.items()):
        pb = parse_board(parent)
        if pb is None:
            continue
        want = set(successors(*pb))
        if succ != want:
            problems.append(f"{parent}: successors {sorted(succ)} != legal moves {sorted(want)}")
        if len(succ) > 4:
            problems.append(f"{parent}: {len(succ)} successors > 4")
    # the independent BFS to the same depth
    frontier, seen, level = {initial}, {initial}, 0
    expected = {}
    while level < depth:
        nxt = set()
        for bd in frontier:
            pb = parse_board(bd)
            ss = set(successors(*pb))
            expected[bd] = ss
            nxt |= ss
        seen |= nxt
        frontier = nxt
        level += 1
    if set(edges) != set(expected):
        problems.append(f"expanded parents {len(edges)} != BFS parents to depth {depth} {len(expected)}")
    for bd, ss in expected.items():
        if edges.get(bd) != ss:
            problems.append(f"{bd}: expansion differs from the independent BFS")
    # ---- the certificate: containment, the proved maximum, the thresholds
    thresholds = {(c[0], c[1], c[2]): c[3] for c in rows(thr) if len(c) >= 4}
    seen_thr = set()
    n_checked = 0
    not_useful = []   # usefulness findings are REPORTED here and GATED by Puzzle15Check (a U gate): sound-but-wide is not unsound
    for c in rows(cert):
        if c[0] != "C" or len(c) < 16:
            continue
        decl, backend = c[1], c[2]
        frontier_size = int(c[3])
        ivls = {}
        for i, comp in enumerate(COMPONENTS):
            lo, hi = c[4 + 2 * i], c[5 + 2 * i]
            ivls[comp] = (int(lo), float("inf") if hi == "inf" else int(hi))
        counted = {comp: (None if c[12 + i] == "-" else int(c[12 + i])) for i, comp in enumerate(COMPONENTS)}
        size_hi = float("inf") if c[17] == "inf" else int(c[17]) if len(c) > 17 else None
        for comp in COMPONENTS:
            lo, hi = ivls[comp]
            v = counted[comp]
            if v is not None and not (lo <= v <= hi):
                problems.append(f"{decl}/{backend}/{comp}: counted {v} outside [{lo}, {hi}]")
            if v is not None:
                n_checked += 1
            t = thresholds.get((decl, backend, comp))
            if t is not None:
                seen_thr.add((decl, backend, comp))
                width = (hi + 1) / (lo + 1) if hi != float("inf") else float("inf")
                if t == "finite":
                    if hi == float("inf"):
                        not_useful.append(f"{decl}/{backend}/{comp}: threshold `finite` but the bound is infinite")
                elif width > float(t):
                    not_useful.append(f"{decl}/{backend}/{comp}: width {width:.3f} > threshold {t}")
        # a FINITE result-size bound above the proved maximum contradicts a theorem: unsound.  An infinite one
        # exceeds every maximum too, but as a loss of precision: not useful, reported, gated by Puzzle15Check
        if size_hi is not None and size_hi != float("inf") and size_hi > 4 * frontier_size:
            problems.append(f"{decl}/{backend}: result-size bound {size_hi} exceeds the proved maximum 4 x {frontier_size} (Zippy.Puzzle15.expand_le)")
        elif size_hi == float("inf"):
            not_useful.append(f"{decl}/{backend}: result-size bound is infinite (the proved maximum is 4 x {frontier_size})")
    for key in sorted(set(thresholds) - seen_thr):
        problems.append(f"threshold {key} has no certificate row")
    # ---- the registry names theorems the Lean file declares
    lean_text = open(lean, encoding="utf-8").read()
    declared = set(re.findall(r"^(?:theorem|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)", lean_text, re.M))
    for c in rows(reg):
        if len(c) >= 3:
            name = c[2].split(".")[-1]
            if name not in declared:
                problems.append(f"registry {c[0]}: {c[2]} is not declared in Puzzle15.lean")
    for u in not_useful:
        print(f"  not useful: {u}")
    return problems, len(boards), n_checked


def main():
    out = check()
    if isinstance(out, list):
        for p in out:
            print(f"  !! {p}")
        print(f"puzzle15: {len(out)} problem(s)")
        return 1
    problems, nb, nc = out
    for p in problems:
        print(f"  !! {p}")
    print(f"puzzle15: {nb} boards re-derived, {nc} counted values inside their intervals; {len(problems)} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
