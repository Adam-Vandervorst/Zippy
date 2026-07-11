#!/usr/bin/env python3
"""Extract rule-only preludes from formal.egg:
  formal-prelude.egg       — the full reference (whole-set equality differentials; needs acu+rotation)
  formal-elem-prelude.egg  — WITHOUT the union/intersection rotation rules: for membership-observation
                             (ElemP) consumers whose checks are shape-free.  Rotation re-chains
                             balanced union trees, turning parallel log-depth distribution into
                             quadratic chain churn — dropping it keeps program-sized terms tractable.
"""
import re, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
s = (root / "formal.egg").read_text()
nocomment = re.sub(r";[^\n]*", "", s)
forms, depth, cur = [], 0, []
for ch in nocomment:
    if ch == "(": depth += 1
    if depth > 0: cur.append(ch)
    if ch == ")":
        depth -= 1
        if depth == 0: forms.append("".join(cur)); cur = []
KEEP = ("(datatype", "(relation", "(ruleset", "(rewrite", "(birewrite", "(rule")
kept = [x for x in forms if x.startswith(KEEP)]
ROT = ("(rewrite (Union (Union x y) z) (Union x (Union y z)))",
       "(rewrite (Intersection (Intersection x y) z) (Intersection x (Intersection y z)))")
hdr = ("; AUTO-EXTRACTED from formal.egg by scripts/extract_formal_preludes.py — do not edit.\n"
       "; Schedules: whole-set equality (repeat N (run) (run acu) (saturate paths) (run neg));\n"
       ";            ElemP membership   (repeat N (run) (saturate paths) (run neg)).\n\n")
(root / "zipper-egg-tests" / "formal-prelude.egg").write_text(hdr + "\n".join(kept) + "\n")
lean = [x for x in kept if x not in ROT]
(root / "zipper-egg-tests" / "formal-elem-prelude.egg").write_text(
    hdr.replace("do not edit.", "do not edit.  ROTATION-FREE variant (see docstring).") + "\n".join(lean) + "\n")
print(f"full: {len(kept)} forms; elem: {len(lean)} forms")
