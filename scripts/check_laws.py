#!/usr/bin/env python3
"""Law-registry checker: every optimiser source law has a per-law entry with a live certificate.

Verifies, against proofs/laws/REGISTRY.tsv and proofs/STATUS.tsv (written by proofs/run.sh):
  1. every law in SC.sourceLaws (parsed from src/main/scala/Supercompiler.scala) has a registry
     row — a law added to the optimiser without a certificate entry fails CI;
  2. every registry row's certificate files exist; FILE/SCHEMATIC certificates must be PROVED
     in STATUS.tsv (an OPEN or COUNTERMODEL verdict, or a file unknown to proofs/run.sh, fails);
  3. the previously-missing algebra laws stay present (composition assoc/right-distributivity,
     De Morgan/absorption/distributivity, wrap-as-composition, restriction idempotence,
     raffination partition, head·tails∪ covering, guard hoisting, Iter fusion).
"""
import pathlib, re, sys

root = pathlib.Path(__file__).resolve().parent.parent
bad = 0

# 1. SC.sourceLaws names
sc = (root / "src/main/scala/Supercompiler.scala").read_text()
start = sc.find("val sourceLaws")
end = sc.find("val simplifyRules", start)
if start < 0 or end < 0:
    print("cannot locate SC.sourceLaws in Supercompiler.scala"); sys.exit(1)
sc_laws = re.findall(r'"([\w-]+)"\s*->', sc[start:end])

# registry + status
reg = {}
for line in (root / "proofs/laws/REGISTRY.tsv").read_text().splitlines():
    if line.startswith("#") or not line.strip():
        continue
    name, kind, certs, note = line.split("\t")
    reg[name] = (kind, certs, note)

status = {}
for line in (root / "proofs/STATUS.tsv").read_text().splitlines():
    parts = line.split("\t")
    if len(parts) == 4:
        status[parts[0]] = parts[3]

for law in sc_laws:
    if law not in reg:
        print(f"SC source law '{law}' has NO registry entry"); bad += 1

REQUIRED = ["comp-assoc", "comp-rdistrib", "demorgan-sub", "absorption", "inter-distrib",
            "wrap-as-comp", "restrict-idem", "restrict-self", "raffination-partition",
            "head-tails-cover", "guard-hoist", "iter-fusion"]
for r in REQUIRED:
    if r not in reg:
        print(f"required algebra law '{r}' missing from the registry"); bad += 1

counts = {"FILE": 0, "SCHEMATIC": 0, "GROUND": 0, "DEFINITIONAL": 0}
for name, (kind, certs, note) in reg.items():
    counts[kind] = counts.get(kind, 0) + 1
    if certs in ("-", ""):
        if kind in ("FILE", "SCHEMATIC"):
            print(f"{name}: kind {kind} but no certificate file"); bad += 1
        continue
    for cert in certs.split(","):
        cert = cert.strip()
        if "*" in cert:      # family glob (GROUND rows)
            if not list((root / "proofs").glob(cert)):
                print(f"{name}: certificate family {cert} matches no files"); bad += 1
            continue
        cpath = root / "proofs" / cert
        if not cpath.exists():
            print(f"{name}: certificate {cert} does not exist"); bad += 1
            continue
        if kind in ("FILE", "SCHEMATIC"):
            key = cert.replace(".smt2", "")
            verdict = status.get(key)
            if verdict is None:
                print(f"{name}: certificate {cert} not covered by proofs/run.sh"); bad += 1
            elif not verdict.startswith("PROVED"):
                print(f"{name}: certificate {cert} verdict is {verdict}"); bad += 1

print(f"registry: {len(reg)} laws ({', '.join(f'{k}={v}' for k, v in counts.items())}); "
      f"SC source laws: {len(sc_laws)}/{len(sc_laws) - sum(1 for l in sc_laws if l not in reg)} covered")
print(f"problems: {bad}")
sys.exit(1 if bad else 0)
