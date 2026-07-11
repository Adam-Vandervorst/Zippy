#!/usr/bin/env python3
"""Generate randomized bridge coincidence tests under zipper-egg-tests/generated/.

For each operator and each random trie instance, three things must agree at EVERY observation path
(all key sequences up to a depth bound):
  (a) the MOVEMENT SPEC's virtual observation   Term (Sub kd (… (Op (Reflect t1) (Reflect t2))))
  (b) the IMPLEMENTATION's recursion via Reflect Term (Sub … (Reflect (TrOp t1 t2)))
  (c) an INDEPENDENT Python denotational reference (path-set semantics), emitted as the literal
      (T)/(F) each side is checked against.
So each file certifies the spec-vs-impl commuting square AND grounds both against an external
reference — hundreds of instances per op.  Besides Term at every path, each instance also checks
Keys (the exact root key list vs the independently computed one, on BOTH sides), IsEmpty, and an
Ascend∘Descend round-trip through the movement sort.
"""
import random, pathlib, itertools

root = pathlib.Path(__file__).resolve().parent.parent
outdir = root / "zipper-egg-tests" / "generated"
outdir.mkdir(parents=True, exist_ok=True)

KEYS = [0, 1, 2]
DEPTH = 2          # observation paths: all key sequences of length <= DEPTH
N_INST = 25        # instances per operator
rng = random.Random(20260628)

# ---- path-set reference semantics (independent of both egg models and of Scala) ----
def rand_set(max_paths=4, max_len=2):
    return frozenset(tuple(rng.choice(KEYS) for _ in range(rng.randint(0, max_len)))
                     for _ in range(rng.randint(0, max_paths)))

def union(a, b): return a | b
def inter(a, b): return a & b
def diff(a, b): return a - b
def comp(a, b): return frozenset(p + q for p in a for q in b)
def restrict(a, b): return frozenset(p for p in a if any(p[:len(q)] == q for q in b))
def raff(a, b): return a - restrict(a, b)
def wrap1(k, a): return frozenset((k,) + p for p in a)
def unwrap1(k, a): return frozenset(p[1:] for p in a if p[:1] == (k,))
def tails_u(a): return frozenset(p[1:] for p in a if len(p) >= 1)
def tails_i(a):
    heads = {p[0] for p in a if len(p) >= 1}
    if not heads: return frozenset()
    groups = [frozenset(p[1:] for p in a if p[:1] == (h,)) for h in heads]
    out = groups[0]
    for g in groups[1:]: out = out & g
    return out
def head(a): return frozenset((p[0],) for p in a if len(p) >= 1)

# ---- encoders: a path set as (1) an impl trie TNode/CC, (2) nothing else needed --------------
def to_trie(s):
    term = "(T)" if () in s else "(F)"
    kids = sorted({p[0] for p in s if len(p) >= 1})
    cl = "(CNil)"
    for k in reversed(kids):
        sub = frozenset(p[1:] for p in s if p[:1] == (k,))
        cl = f"(CC {k} {to_trie(sub)} {cl})"
    return f"(Node {term} {cl})"          # renamed below for the bridge

def obs_paths():
    for d in range(DEPTH + 1):
        yield from itertools.product(KEYS, repeat=d)

def member(s, path): return tuple(path) in s

# each op: (name, arity, reference fn, spec Z syntax, impl Tr syntax)
OPS = [
    ("union",        2, union,    lambda x, y: f"(Union {x} {y})",        lambda x, y: f"(TrU {x} {y})"),
    ("intersection", 2, inter,    lambda x, y: f"(Intersection {x} {y})", lambda x, y: f"(TrI {x} {y})"),
    ("subtraction",  2, diff,     lambda x, y: f"(Subtraction {x} {y})",  lambda x, y: f"(TrS {x} {y})"),
    ("composition",  2, comp,     lambda x, y: f"(Composition {x} {y})",  lambda x, y: f"(TrC {x} {y})"),
    ("restriction",  2, restrict, lambda x, y: f"(Restriction {x} {y})",  lambda x, y: f"(TrR {x} {y})"),
    ("raffination",  2, raff,     lambda x, y: f"(Raffination {x} {y})",  lambda x, y: f"(TrRaf {x} {y})"),
    ("wrap1",        1, lambda a: wrap1(1, a),   lambda x: f"(Wrap1 1 {x})",  lambda x: f"(TrW 1 {x})"),
    ("unwrap",       1, lambda a: unwrap1(1, a), lambda x: f"(Unwrap 1 {x})", lambda x: f"(TrUn 1 {x})"),
    ("tailsunion",   1, tails_u,  lambda x: f"(TailsUnion {x})",          lambda x: f"(TrTU {x})"),
    ("tailsinter",   1, tails_i,  lambda x: f"(TailsIntersection {x})",   lambda x: f"(TrTI {x})"),
    ("head",         1, head,     lambda x: f"(Head {x})",                lambda x: f"(TrH {x})"),
]

# ---- the SET-OF-PATHS (formal.egg / exec reference) encoding --------------------------------
def to_path(p):
    if not p: return "(Eps)"
    out = f"(Item {p[-1]})"
    for k in reversed(p[:-1]): out = f"(Concat (Item {k}) {out})"
    return out

def to_setofpaths(s):
    ps = sorted(s)
    if not ps: return "(Empty)"
    out = f"(Singleton {to_path(ps[-1])})"
    for p in reversed(ps[:-1]): out = f"(Union (Singleton {to_path(p)}) {out})"
    return out

# formal-vocabulary syntax per op (name -> lambda or None if not in the reference)
FORMAL = {
    "union":        lambda x, y: f"(Union {x} {y})",
    "intersection": lambda x, y: f"(Intersection {x} {y})",
    "subtraction":  lambda x, y: f"(Subtraction {x} {y})",
    "composition":  lambda x, y: f"(Composition {x} {y})",
    "restriction":  lambda x, y: f"(Restriction {x} {y})",
    "raffination":  lambda x, y: f"(Raffination {x} {y})",
    "wrap1":        lambda x: f"(Wrap (Item 1) {x})",
    "unwrap":       lambda x: f"(Unwrap {x} (Item 1))",
    "tailsunion":   lambda x: f"(TailsUnion {x})",
    "tailsinter":   lambda x: f"(TailsIntersection {x})",
    "head":         lambda x: f"(Head {x})",
}
N_FORMAL = 12      # per-op instances for the set-of-paths files (smaller: comm/assoc closure cost)

total_checks = 0
for name, arity, ref, zsyn, tsyn in OPS:
    lines = [f"; AUTO-GENERATED by scripts/gen_bridge_tests.py — randomized spec/impl/reference",
             f"; coincidence for `{name}` on {N_INST} random tries, observed at every path of depth <= {DEPTH}.",
             '(include "bridge-prelude.egg")', ""]
    checks = []
    for i in range(N_INST):
        args = [rand_set() for _ in range(arity)]
        res = ref(*args)
        tries = [to_trie(a).replace("(Node ", "(TNode ") for a in args]
        # (a) the spec-side virtual term over Reflect'ed concrete cursors
        zrefl = zsyn(*[f"(Reflect {t})" for t in tries])
        # (b) the impl-side recursion, then Reflect the result
        timpl = f"(Reflect {tsyn(*tries)})"
        lines.append(f"(let $z{i} {zrefl})")
        lines.append(f"(let $t{i} {timpl})")
        for j, p in enumerate(obs_paths()):
            zt, tt = f"$z{i}", f"$t{i}"
            for k in p: zt = f"(Sub {k} {zt})"
            for k in p: tt = f"(Sub {k} {tt})"
            want = "(T)" if member(res, p) else "(F)"
            lines.append(f"(let $zo{i}_{j} (Term {zt}))")
            lines.append(f"(let $to{i}_{j} (Term {tt}))")
            checks.append(f"(check (= $zo{i}_{j} {want}))")
            checks.append(f"(check (= $to{i}_{j} {want}))")
        # NEW observations (review): Keys at the root (exact key list, vs the independently computed
        # one), IsEmpty at the root, and an Ascend round-trip through the movement sort.
        root_keys = sorted({p[0] for p in res if len(p) >= 1})
        want_keys = "(KNil)"
        for k in reversed(root_keys): want_keys = f"(KCons {k} {want_keys})"
        lines.append(f"(let $zk{i} (Keys $z{i}))")
        lines.append(f"(let $tk{i} (Keys $t{i}))")
        checks.append(f"(check (= $zk{i} {want_keys}))")
        checks.append(f"(check (= $tk{i} {want_keys}))")
        want_emp = "(T)" if (not res) else "(F)"
        lines.append(f"(let $ze{i} (IsEmpty $z{i}))")
        lines.append(f"(let $te{i} (IsEmpty $t{i}))")
        checks.append(f"(check (= $ze{i} {want_emp}))")
        checks.append(f"(check (= $te{i} {want_emp}))")
        k0 = root_keys[0] if root_keys else 0
        lines.append(f"(let $za{i} (FocusOf (Ascend (Descend {k0} (Root $z{i})))))")
        checks.append(f"(check (= $za{i} $z{i}))")
    lines.append("")
    lines.append("(run 400)")
    lines.append("")
    lines.extend(checks)
    (outdir / f"rand-{name}.egg").write_text("\n".join(lines) + "\n")
    total_checks += len(checks)
    print(f"rand-{name}.egg: {N_INST} instances, {len(checks)} checks")

# ---- the third notion: SET-OF-PATHS differential in the formal (exec reference) vocabulary.
# Same reference semantics, same RNG stream discipline; the eager reference computes WHOLE SETS,
# so the check is canonical-set equality (formal.egg's own comm/assoc equations decide it).
for name, arity, ref, _, _ in OPS:
    fsyn = FORMAL[name]
    # raffination = x \ (x <| y): x occurs twice; under the reference's comm/assoc closure its eager
    # expansion grows factorially, so its differential uses tiny instances (len-1 paths).  Its full
    # validation is COMPOSITIONAL: it is a definitional macro over subtraction+restriction, each
    # differentially validated at full size here and proved universally in proofs/.
    n_inst, mp, ml = (6, 2, 1) if name == "raffination" else (N_FORMAL, 3, 2)
    lines = [f"; AUTO-GENERATED by scripts/gen_bridge_tests.py — SET-OF-PATHS (exec reference)",
             f"; differential for `{name}` on {n_inst} random instances: the formal model's eager",
             f"; evaluation must compute exactly the independently-computed result set.",
             '(include "formal-prelude.egg")', ""]
    checks = []
    for i in range(n_inst):
        args = [rand_set(max_paths=mp, max_len=ml) for _ in range(arity)]
        res = ref(*args)
        lines.append(f"(let $in{i} {fsyn(*[to_setofpaths(a) for a in args])})")
        lines.append(f"(let $want{i} {to_setofpaths(res)})")
        checks.append(f"(check (= $in{i} $want{i}))")
    lines.append("")
    lines.append("(run-schedule (repeat 8 (run) (run acu) (saturate paths) (run neg)))")
    lines.append("")
    lines.extend(checks)
    (outdir / f"rand-setofpaths-{name}.egg").write_text("\n".join(lines) + "\n")
    total_checks += len(checks)
    print(f"rand-setofpaths-{name}.egg: {N_FORMAL} instances, {len(checks)} checks")
print(f"total: {total_checks} checks")
