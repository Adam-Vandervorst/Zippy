#!/usr/bin/env python3
"""Run the MORKL proof gate.

Scala is the source of truth for generated artifacts:

1. `morkl.ProofArtifactGeneratorMain` writes SMT2 and TPTP files plus a
   manifest consumed by this runner.
2. `morkl.generateZipperEggTests` writes the shared-prelude `formal.egg` and
   `zipper.egg` introductions plus the independently runnable example files.
3. `morkl.generateCornerstoneProofArtifacts` writes end-to-end equivalence
   certificates for the cornerstone examples.
 4. `morkl.generateOpenProgramProofArtifacts` writes symbolic open-program
   equivalence obligations over bounded arbitrary input spaces plus structural
   full-program FOL obligations for the cornerstone examples.
5. This script only orchestrates external tools: Vampire, Z3, and egglog.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Sequence


MUNIT_DEP = "org.scalameta::munit:1.2.1"
COLLECTION_CONTRIB_DEP = "org.scala-lang.modules::scala-collection-contrib:0.3.0"


@dataclasses.dataclass(frozen=True)
class Artifact:
    kind: str
    name: str
    expected: str
    artifact: Path
    note: str = ""


@dataclasses.dataclass(frozen=True)
class Result:
    name: str
    expected: str
    actual: str
    ok: bool
    artifact: Path | str
    note: str = ""


@dataclasses.dataclass(frozen=True)
class OperationalRule:
    rule_id: str
    kind: str
    line: int
    operations: tuple[str, ...]
    tier: str
    status: str
    artifacts: tuple[str, ...]
    note: str
    rule: str


@dataclasses.dataclass(frozen=True)
class OperationalManifestStats:
    total: int
    proved_unbounded: int
    proved_bounded: int
    axiom_elsewhere: int
    unproved: int
    mixed_bounded: int
    bounded_only: int

    @property
    def proof_debt(self) -> int:
        return self.proved_bounded + self.axiom_elsewhere + self.unproved


def manifest_unescape(text: str) -> str:
    out: list[str] = []
    i = 0
    while i < len(text):
        if text[i] == "\\" and i + 1 < len(text):
            nxt = text[i + 1]
            if nxt == "t":
                out.append("\t")
            elif nxt == "n":
                out.append("\n")
            else:
                out.append(nxt)
            i += 2
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def manifest_escape(text: str) -> str:
    return text.replace("\\", "\\\\").replace("\t", "\\t").replace("\n", "\\n")


def read_manifest(path: Path, root: Path) -> list[Artifact]:
    lines = [line for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    if not lines:
        raise RuntimeError(f"empty proof manifest: {path}")
    header = lines[0].split("\t")
    expected_header = ["kind", "name", "expected", "artifact", "note"]
    if header != expected_header:
        raise RuntimeError(f"bad manifest header in {path}: {header}")
    artifacts: list[Artifact] = []
    for line in lines[1:]:
        parts = [manifest_unescape(part) for part in line.split("\t")]
        if len(parts) != 5:
            raise RuntimeError(f"bad manifest row in {path}: {line}")
        artifact = Path(parts[3])
        if not artifact.is_absolute():
            artifact = root / artifact
        artifacts.append(Artifact(parts[0], parts[1], parts[2], artifact, parts[4]))
    return artifacts


def validate_product_mask_artifacts(artifacts: list[Artifact], root: Path) -> Result:
    """Guard the bounded product derivative proof against hand-picked masks.

    The finite-language SMT encoding must use a generated ProductClosed(X,Y)
    assumption: it forbids exactly the left/right path pairs whose concatenation
    would leave the bounded universe. This check deliberately runs before Z3 so
    manifest-only runs still fail if that proof obligation regresses to an
    undocumented or hand-picked mask.
    """
    by_name = {artifact.name: artifact for artifact in artifacts}
    required_names = (
        "child_product_a",
        "child_product_b",
        "bad_child_product_without_length_guard_negative_control",
        "set_child_product_derivative",
        "set_terminal_product",
        "set_product_prefix_closure_left_progress_fo",
    )
    missing = [name for name in required_names if name not in by_name]
    errors: list[str] = []
    if missing:
        errors.append("missing manifest artifacts: " + ", ".join(missing))

    for name in ("child_product_a", "child_product_b"):
        artifact = by_name.get(name)
        if artifact is None:
            continue
        if artifact.kind != "z3" or artifact.expected != "unsat":
            errors.append(f"{name} must be a Z3 unsat law, got {artifact.kind}/{artifact.expected}")
        if not artifact.artifact.exists():
            errors.append(f"{name} artifact does not exist: {display_path(artifact.artifact, root)}")
            continue
        text = artifact.artifact.read_text(encoding="utf-8")
        required_text = (
            "assumption: ProductClosed(left,right)",
            "principle: no concatenation escapes the bounded universe",
            "generated guard: forbids exactly",
            "not a hand-picked mask",
        )
        for needle in required_text:
            if needle not in text:
                errors.append(f"{name} artifact is missing `{needle}`")
        if "ProductClosed" not in artifact.note:
            errors.append(f"{name} manifest note must name ProductClosed")

    negative = by_name.get("bad_child_product_without_length_guard_negative_control")
    if negative is not None:
        if negative.kind != "z3" or negative.expected != "sat":
            errors.append(
                "bad_child_product_without_length_guard_negative_control must be a Z3 sat negative control, "
                f"got {negative.kind}/{negative.expected}"
            )
        if not negative.artifact.exists():
            errors.append(f"negative-control artifact does not exist: {display_path(negative.artifact, root)}")
        else:
            text = negative.artifact.read_text(encoding="utf-8")
            if "ProductClosed" in text:
                errors.append("negative-control artifact must remain unguarded by ProductClosed")
        if "without the no-concatenation-escapes-universe guard is false" not in negative.note:
            errors.append("negative-control manifest note must explain why the unguarded law is false")

    for name in ("set_child_product_derivative", "set_terminal_product"):
        artifact = by_name.get(name)
        if artifact is not None and (artifact.kind != "vampire" or artifact.expected != "Theorem"):
            errors.append(f"{name} must be a Vampire theorem, got {artifact.kind}/{artifact.expected}")

    if errors:
        return Result(
            "product-guard artifact invariant",
            "ProductClosed+negative-control",
            "invalid",
            False,
            "proofs/proof_manifest.tsv",
            "; ".join(errors),
        )
    return Result(
        "product-guard artifact invariant",
        "ProductClosed+negative-control",
        "ok",
        True,
        "proofs/proof_manifest.tsv",
        "child_product_a/b use generated ProductClosed guards and the unguarded negative control remains sat",
    )


NEGATIVE_CONTROL_FAMILIES: dict[str, tuple[str, ...]] = {
    "union": ("bad_union_as_intersection_generated_negative_control",),
    "intersection": ("bad_intersection_as_union_generated_negative_control",),
    "diff": ("bad_diff_as_intersection_generated_negative_control",),
    "restriction-raffination": ("bad_restriction_as_raffination_generated_negative_control",),
    "wrap-unwrap": ("bad_wrap_unwrap_wrong_prefix_generated_negative_control",),
    "product": ("bad_child_product_without_length_guard_negative_control",),
    "child-union": (
        "bad_child_union_as_child_intersection_generated_negative_control",
        "bad_child_same_head_union_a_drops_second_generated_negative_control",
        "bad_child_same_head_union_b_drops_second_generated_negative_control",
    ),
    "tails-union": (
        "bad_tails_union_as_head_generated_negative_control",
        "bad_child_tails_union_a_drops_b_frontier_generated_negative_control",
    ),
    "tails-intersection": ("bad_tails_intersection_as_tails_union_generated_negative_control",),
    "closures": (
        "bad_prefix_closure_identity_generated_negative_control",
        "bad_suffix_closure_identity_generated_negative_control",
        "bad_tails_closure_identity_generated_negative_control",
        "bad_tails_closure_without_base_generated_negative_control",
    ),
    "antimirov-frontier": (
        "bad_antimirov_suffix_frontier_state_is_source_child_generated_negative_control",
        "bad_antimirov_tails_frontier_state_is_source_child_generated_negative_control",
    ),
    "nonempty": ("bad_nonempty_identity_generated_negative_control",),
    "head": ("bad_head_identity_generated_negative_control",),
    "patch-context": ("bad_patch_child_identity_generated_negative_control",),
    "iteration": (
        "bad_iteration_reconstruct_identity_generated_negative_control",
        "bad_iteration_tail_union_as_intersection_generated_negative_control",
        "bad_iteration_range_tail_first_is_tail_union_generated_negative_control",
        "bad_iteration_range_reconstruct_first_is_nonempty_generated_negative_control",
    ),
    "fixpoint": (
        "bad_fixpoint_tail_identity_generated_negative_control",
        "bad_fixpoint_tail_without_base_generated_negative_control",
        "bad_fixpoint_head_identity_generated_negative_control",
        "bad_fixpoint_reconstruct_as_nonempty_generated_negative_control",
        "bad_fixpoint_range_tail_first_as_tail_closure_generated_negative_control",
    ),
    "range": (
        "bad_range_first_is_full_generated_negative_control",
        "bad_range_last_is_full_generated_negative_control",
        "bad_range_drop_last_is_full_generated_negative_control",
        "bad_range_first_distributes_over_union_generated_negative_control",
        "bad_range_last_distributes_over_union_generated_negative_control",
    ),
}


def validate_negative_control_families(artifacts: list[Artifact], root: Path) -> Result:
    """Ensure every major law family has live Z3 sat negative controls."""
    by_name = {artifact.name: artifact for artifact in artifacts}
    errors: list[str] = []
    checked = 0
    for family, names in NEGATIVE_CONTROL_FAMILIES.items():
        missing = [name for name in names if name not in by_name]
        if missing:
            errors.append(f"{family}: missing {', '.join(missing)}")
            continue
        for name in names:
            artifact = by_name[name]
            checked += 1
            if artifact.kind != "z3" or artifact.expected != "sat":
                errors.append(f"{family}: {name} must be a Z3 sat negative control, got {artifact.kind}/{artifact.expected}")
            if not artifact.artifact.exists():
                errors.append(f"{family}: artifact missing at {display_path(artifact.artifact, root)}")
    if errors:
        return Result(
            "negative-control family invariant",
            "all-families-sat",
            "invalid",
            False,
            "proofs/proof_manifest.tsv",
            "; ".join(errors),
        )
    return Result(
        "negative-control family invariant",
        "all-families-sat",
        "ok",
        True,
        "proofs/proof_manifest.tsv",
        f"{len(NEGATIVE_CONTROL_FAMILIES)} families covered by {checked} Z3 sat negative controls",
    )


SYMBOL_COVERAGE_FAMILIES: dict[str, tuple[str, ...]] = {
    "wrap-unwrap-left-inverse": ("wrap_unwrap_left_inverse_a", "wrap_unwrap_left_inverse_b"),
    "wrap-unwrap-restriction": ("wrap_unwrap_restriction_a", "wrap_unwrap_restriction_b"),
    "child-union": ("child_union_a", "child_union_b"),
    "child-same-head-union": ("child_same_head_union_a", "child_same_head_union_b"),
    "child-intersection": ("child_intersection_a", "child_intersection_b"),
    "child-diff": ("child_diff_a", "child_diff_b"),
    "child-empty": ("child_empty_a", "child_empty_b"),
    "child-epsilon": ("child_epsilon_a", "child_epsilon_b"),
    "child-singleton-hit": ("child_singleton_hit_a", "child_singleton_hit_b"),
    "child-singleton-miss": ("child_singleton_miss_a_b", "child_singleton_miss_b_a"),
    "child-concat-hit": ("child_concat_hit_a", "child_concat_hit_b"),
    "child-concat-miss": ("child_concat_miss_a_b", "child_concat_miss_b_a"),
    "child-product": ("child_product_a", "child_product_b"),
    "child-restriction": ("child_restriction_a", "child_restriction_b"),
    "frontier-tail-union": ("frontier_tail_union_a_is_child", "frontier_tail_union_b_is_child"),
    "child-tails-union": ("child_tails_union_a", "child_tails_union_b"),
    "nonempty-child": ("nonempty_child_a", "nonempty_child_b"),
    "patch-child-hit": ("patch_child_hit_a", "patch_child_hit_b"),
    "patch-child-miss": ("patch_child_miss_a", "patch_child_miss_b"),
    "patch-child-identity": ("patch_child_identity_a", "patch_child_identity_b"),
    "suffix-closure-child": ("suffix_closure_child_derivative_a", "suffix_closure_child_derivative_b"),
    "tails-closure-child": ("child_tails_closure_derivative_a", "child_tails_closure_derivative_b"),
    "antimirov-suffix-frontier": ("antimirov_suffix_frontier_state_child_a", "antimirov_suffix_frontier_state_child_b"),
    "antimirov-tails-frontier": ("antimirov_tails_frontier_state_child_a", "antimirov_tails_frontier_state_child_b"),
    "range-wrap-first": ("range_first_wrap_a", "range_first_wrap_b"),
    "range-wrap-last": ("range_last_wrap_a", "range_last_wrap_b"),
    "range-wrap-drop-last": ("range_drop_last_wrap_a", "range_drop_last_wrap_b"),
}


def has_symmetry_artifact(family: str, by_name: dict[str, Artifact]) -> bool:
    normalized = family.replace("-", "_")
    candidates = (
        f"{normalized}_symmetry",
        f"{normalized}_symmetric",
        f"symmetry_{normalized}",
    )
    return any(
        name in by_name and by_name[name].expected in {"unsat", "Theorem", "exit-0"}
        for name in candidates
    )


def validate_symbol_coverage_artifacts(artifacts: list[Artifact], root: Path) -> Result:
    """Require paired a/b representatives unless an explicit symmetry proof exists."""
    by_name = {artifact.name: artifact for artifact in artifacts}
    errors: list[str] = []
    checked = 0
    for family, names in SYMBOL_COVERAGE_FAMILIES.items():
        if has_symmetry_artifact(family, by_name):
            checked += 1
            continue
        missing = [name for name in names if name not in by_name]
        if missing:
            errors.append(f"{family}: missing {', '.join(missing)} and no symmetry artifact")
            continue
        for name in names:
            artifact = by_name[name]
            checked += 1
            if artifact.kind != "z3" or artifact.expected != "unsat":
                errors.append(f"{family}: {name} must be a Z3 unsat representative, got {artifact.kind}/{artifact.expected}")
            if not artifact.artifact.exists():
                errors.append(f"{family}: artifact missing at {display_path(artifact.artifact, root)}")
    if errors:
        return Result(
            "symbol-coverage invariant",
            "both-symbols-or-symmetry",
            "invalid",
            False,
            "proofs/proof_manifest.tsv",
            "; ".join(errors),
        )
    return Result(
        "symbol-coverage invariant",
        "both-symbols-or-symmetry",
        "ok",
        True,
        "proofs/proof_manifest.tsv",
        f"{len(SYMBOL_COVERAGE_FAMILIES)} families covered by {checked} paired-symbol or symmetry artifacts",
    )


def display_path(path: Path, root: Path) -> Path | str:
    try:
        return path.relative_to(root)
    except ValueError:
        return str(path)


def run_process(name: str, cmd: list[str], cwd: Path, expected: str = "exit-0") -> Result:
    proc = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    actual = f"exit-{proc.returncode}"
    ok = actual == expected
    note = "" if ok else (proc.stdout + "\n" + proc.stderr).strip()
    return Result(name, expected, actual, ok, " ".join(cmd), note)


def run_scala_proof_generator(args: argparse.Namespace, root: Path) -> Result:
    scala_cli = shutil.which("scala-cli")
    if not scala_cli:
        return Result("scala proof artifact generation", "exit-0", "missing", False, "scala-cli", "scala-cli not found on PATH")
    cmd = [
        scala_cli,
        "run",
        "src/main/scala",
        "--server=false",
        "--scala",
        "3.8.1",
        "--source",
        "3.3",
        "--main-class",
        "morkl.ProofArtifactGeneratorMain",
        "--",
        "--alphabet",
        args.alphabet,
        "--max-len",
        str(args.max_len),
        "--out-dir",
        args.out_dir,
        "--vampire-out-dir",
        args.vampire_out_dir,
        "--manifest",
        args.manifest,
    ]
    return run_process("scala proof artifact generation", cmd, root)


def run_scala_egg_generator(root: Path) -> Result:
    scala_cli = shutil.which("scala-cli")
    if not scala_cli:
        return Result("scala egg artifact generation", "exit-0", "missing", False, "scala-cli", "scala-cli not found on PATH")
    cmd = [
        scala_cli,
        "run",
        ".",
        "--test",
        "--server=false",
        "--scala",
        "3.8.1",
        "--source",
        "3.3",
        "--dependency",
        MUNIT_DEP,
        "--dependency",
        COLLECTION_CONTRIB_DEP,
        "--main-class",
        "morkl.generateZipperEggTests",
        "--",
    ]
    return run_process("scala egg artifact generation", cmd, root)


def run_scala_cornerstone_generator(args: argparse.Namespace, root: Path) -> Result:
    scala_cli = shutil.which("scala-cli")
    if not scala_cli:
        return Result("scala cornerstone proof generation", "exit-0", "missing", False, "scala-cli", "scala-cli not found on PATH")
    cmd = [
        scala_cli,
        "run",
        ".",
        "--test",
        "--server=false",
        "--scala",
        "3.8.1",
        "--source",
        "3.3",
        "--dependency",
        MUNIT_DEP,
        "--dependency",
        COLLECTION_CONTRIB_DEP,
        "--main-class",
        "morkl.generateCornerstoneProofArtifacts",
        "--",
        "--out-dir",
        args.example_out_dir,
        "--manifest",
        args.example_manifest,
    ]
    return run_process("scala cornerstone proof generation", cmd, root)


def run_scala_open_program_generator(args: argparse.Namespace, root: Path) -> Result:
    scala_cli = shutil.which("scala-cli")
    if not scala_cli:
        return Result("scala open-program proof generation", "exit-0", "missing", False, "scala-cli", "scala-cli not found on PATH")
    cmd = [
        scala_cli,
        "run",
        ".",
        "--test",
        "--server=false",
        "--scala",
        "3.8.1",
        "--source",
        "3.3",
        "--dependency",
        MUNIT_DEP,
        "--dependency",
        COLLECTION_CONTRIB_DEP,
        "--main-class",
        "morkl.generateOpenProgramProofArtifacts",
        "--",
        "--out-dir",
        args.open_out_dir,
        "--manifest",
        args.open_manifest,
    ]
    return run_process("scala open-program proof generation", cmd, root)


def run_z3(z3: str, artifact: Artifact, root: Path, time_limit: int) -> Result:
    try:
        proc = subprocess.run(
            [z3, f"-T:{time_limit}", str(artifact.artifact)],
            text=True,
            capture_output=True,
            timeout=time_limit + 5,
        )
    except subprocess.TimeoutExpired as exc:
        note = ((exc.stdout or "") + "\n" + (exc.stderr or "")).strip()
        return Result(artifact.name, artifact.expected, "timeout", False, display_path(artifact.artifact, root), note)
    lines = [line.strip() for line in proc.stdout.splitlines() if line.strip()]
    actual = lines[0] if lines else f"exit-{proc.returncode}"
    ok = actual == artifact.expected
    note = "" if ok else (proc.stdout + "\n" + proc.stderr).strip()
    return Result(artifact.name, artifact.expected, actual, ok, display_path(artifact.artifact, root), note)


def run_z3_multicheck(z3: str, artifact: Artifact, root: Path, time_limit: int) -> Result:
    try:
        proc = subprocess.run(
            [z3, f"-T:{time_limit}", str(artifact.artifact)],
            text=True,
            capture_output=True,
            timeout=time_limit + 5,
        )
    except subprocess.TimeoutExpired as exc:
        note = ((exc.stdout or "") + "\n" + (exc.stderr or "")).strip()
        return Result(artifact.name, artifact.expected, "timeout", False, display_path(artifact.artifact, root), note)
    actual_lines = [line.strip() for line in proc.stdout.splitlines() if line.strip()]
    expected_lines = [line.strip() for line in artifact.expected.splitlines() if line.strip()]
    actual = "\n".join(actual_lines) if actual_lines else f"exit-{proc.returncode}"
    ok = actual_lines == expected_lines
    note = "" if ok else (proc.stdout + "\n" + proc.stderr).strip()
    return Result(artifact.name, artifact.expected, actual, ok, display_path(artifact.artifact, root), note)


def vampire_status(output: str) -> str:
    for line in output.splitlines():
        if "SZS status" in line:
            parts = line.strip().split()
            for i, part in enumerate(parts):
                if part == "status" and i + 1 < len(parts):
                    return parts[i + 1]
    stripped = output.strip()
    return stripped.splitlines()[0].strip() if stripped else "no-status"


def run_vampire(vampire: str, artifact: Artifact, root: Path, time_limit: int) -> Result:
    mode = "portfolio"
    try:
        proc = subprocess.run(
            [vampire, "--mode", mode, "--input_syntax", "tptp", "--proof", "tptp", "--time_limit", str(time_limit), str(artifact.artifact)],
            text=True,
            capture_output=True,
            timeout=time_limit + 30,
        )
    except subprocess.TimeoutExpired as exc:
        combined = ((exc.stdout or "") + "\n" + (exc.stderr or "")).strip()
        return Result(artifact.name, artifact.expected, "timeout", False, display_path(artifact.artifact, root), f"mode={mode}\n{combined}")
    combined = (proc.stdout + "\n" + proc.stderr).strip()
    actual = vampire_status(combined)
    expected_statuses = {part.strip() for part in artifact.expected.split("|")}
    ok = actual in expected_statuses
    note = "" if ok else f"mode={mode}\n{combined}"
    return Result(artifact.name, artifact.expected, actual, ok, display_path(artifact.artifact, root), note)


def termination_solver_artifacts(root: Path) -> tuple[list[Artifact], list[Artifact], list[Artifact], list[Path]]:
    base = root / "terminating"
    vampire = [
        Artifact("vampire", "termination:least_fixpoint_unique", "Theorem", base / "least_fixpoint_unique.p", "curated least-fixpoint uniqueness theorem"),
        Artifact("vampire", "termination:bounded_growth_decrease", "Theorem", base / "bounded_growth_decrease.p", "curated finite-growth strict decrease theorem"),
        Artifact("vampire", "termination:transitive_equiv", "Theorem", base / "transitive_equiv.p", "curated transitive-closure equivalence theorem"),
        Artifact("vampire", "termination:datalog_a_terminates", "Theorem", base / "datalog_a_terminates.p", "curated Datalog A termination theorem"),
        Artifact("vampire", "termination:datalog_b_naive_terminates", "Theorem", base / "datalog_b_naive_terminates.p", "curated naive Datalog B termination theorem"),
        Artifact("vampire", "termination:datalog_b_seminaive_terminates", "Theorem", base / "datalog_b_seminaive_terminates.p", "curated semi-naive Datalog B termination theorem"),
    ]
    z3 = [
        Artifact("z3", "termination:transitive_equiv_smt", "unsat", base / "transitive_equiv.smt2", "curated quantified SMT transitive equivalence check"),
    ]
    z3_multicheck = [
        Artifact(
            "z3-multicheck",
            "termination:no_infinite_descent",
            "unsat\nunsat\nunsat",
            base / "no_infinite_descent.smt2",
            "curated three-step induction arithmetic check",
        ),
    ]
    egg = [
        base / "intro.egg",
        base / "total_functions.egg",
    ]
    return vampire, z3, z3_multicheck, egg


def path_count(alphabet: Sequence[str], max_len: int) -> int:
    total = 0
    size = len(alphabet)
    for length in range(max_len + 1):
        total += size ** length
    return total


OPERATION_NAMES = (
    "UnionOp",
    "JoinAllOp3",
    "IntersectionOp",
    "MeetAllOp3",
    "DiffOp",
    "RestrictionOp",
    "RaffinationOp",
    "ConcatOp",
    "WrapOp",
    "UnwrapOp",
    "NonEmptyOp",
    "TailsUnionOp",
    "FrontierUnionOp",
    "FrontierChildUnionOp",
    "FrontierTailUnionOp",
    "FrontierStateOp",
    "TailsIntersectionOp",
    "PrefixClosureOp",
    "PrefixClosureBelowOp",
    "SuffixClosureOp",
    "TailsClosureOp",
    "RangeOp",
    "RangeFirstOp",
    "RangeLastOp",
    "RangeDropLastOp",
    "HeadOp",
    "IterOp",
    "BoundHeadOp",
    "BoundTailOp",
    "InstantiateOp",
    "IterBinderOp",
    "IterBranchesOp",
    "iter-independent",
    "IterRangeTailOp",
    "IterRangeReconstructOp",
    "IterPrefixedRangeReconstructOp",
    "FixpointOp",
    "PatchChildOp",
    "TerminalProductChild",
    "tail-frontier",
    "suffix-active",
    "frontier-candidate",
    "frontier-union1-query",
    "frontier-union2-query",
    "frontier-union-result",
    "plugged",
    "cursor",
    "down-move",
    "up-move",
    "next-sibling-move",
    "previous-sibling-move",
    "next-sibling-target",
    "previous-sibling-target",
    "adjacent-before",
    "context-path",
    "cursor-path",
    "needs-first-head",
    "needs-last-head",
    "first-head",
    "last-head",
    "range-first-child-query",
    "range-last-child-query",
    "range-drop-last-child-query",
    "range-child-result",
    "iter-child-query",
    "iter-child-result",
    "fixpoint-child-query",
    "fixpoint-child-result",
    "fixpoint-unfold-query",
    "fixpoint-unfold-result",
    "Descend",
    "Child",
    "TrieZ",
    "EmptyZ",
    "MemoZ",
    "terminal",
    "empty-focus",
    "nonterminal",
    "nonempty-focus",
    "has-key",
    "observed-key",
    "observable-focus",
    "child-focus",
    "absent-key",
    "keyset",
    "single-frontier",
    "KUnion",
    "KIntersection",
    "KDiff",
    "ordered-before",
)


OPERATION_ARTIFACT_HINTS: dict[str, tuple[str, ...]] = {
    "UnionOp": (
        "zipper_union_terminal_equiv",
        "zipper_union_child_equiv",
        "set_child_union_fo",
        "set_union_idempotent_fo",
        "set_union_associative_fo",
        "child_union_a",
        "child_union_b",
        "child_same_head_union_a",
        "child_same_head_union_b",
        "union_idempotent",
        "union_associative",
    ),
    "KUnion": (
        "keyset_union_empty_left_fo",
        "keyset_union_empty_right_fo",
        "keyset_union_idempotent_fo",
    ),
    "JoinAllOp3": ("zipper_union_terminal_equiv", "zipper_union_child_equiv", "set_child_union_fo", "child_union_a", "child_union_b"),
    "IntersectionOp": (
        "zipper_intersection_terminal_equiv",
        "zipper_intersection_child_equiv",
        "set_child_intersection_fo",
        "set_intersection_idempotent_fo",
        "set_intersection_associative_fo",
        "child_intersection_a",
        "child_intersection_b",
        "intersection_associative",
    ),
    "KIntersection": (
        "keyset_intersection_empty_left_fo",
        "keyset_intersection_empty_right_fo",
        "keyset_intersection_idempotent_fo",
        "keyset_intersection_one_hit_fo",
        "keyset_intersection_one_miss_fo",
    ),
    "MeetAllOp3": ("zipper_intersection_terminal_equiv", "zipper_intersection_child_equiv", "child_intersection_a", "child_intersection_b"),
    "DiffOp": (
        "zipper_diff_terminal_equiv",
        "zipper_diff_child_equiv",
        "set_child_diff_fo",
        "set_diff_self_empty_fo",
        "set_diff_union_rhs_fo",
        "child_diff_a",
        "child_diff_b",
        "diff_self_empty",
        "diff_union_rhs",
    ),
    "KDiff": (
        "keyset_diff_empty_left_fo",
        "keyset_diff_empty_right_fo",
        "keyset_diff_self_fo",
        "keyset_diff_one_hit_fo",
        "keyset_diff_one_miss_fo",
    ),
    "MemoZ": (
        "zipper_memo_materialization_equiv",
        "zipper_memo_terminal_equiv",
        "zipper_memo_child_equiv",
    ),
    "EmptyZ": (
        "zipper_emptyz_empty_focus_fo",
        "zipper_emptyz_nonterminal_fo",
        "zipper_keyset_emptyz_fo",
    ),
    "RaffinationOp": (
        "eager_raffination_set_equiv",
        "zipper_raffination_materialization_equiv",
        "arbitrary_zipper_raffination_set_equiv",
        "set_child_raffination_derivative",
        "set_restriction_raffination_partition_fo",
        "set_restriction_raffination_disjoint_fo",
        "restriction_raffination_partition",
        "restriction_raffination_disjoint",
    ),
    "RestrictionOp": (
        "eager_restriction_set_equiv",
        "zipper_restriction_materialization_equiv",
        "arbitrary_zipper_restriction_set_equiv",
        "set_child_restriction_derivative",
        "child_restriction_a",
        "child_restriction_b",
        "restriction_epsilon_identity",
        "restriction_empty_prefixes",
    ),
    "ConcatOp": (
        "eager_product_set_equiv",
        "zipper_product_materialization_equiv",
        "arbitrary_zipper_product_set_equiv",
        "set_child_product_derivative",
        "set_terminal_product",
        "child_product_a",
        "child_product_b",
        "product_epsilon_left",
        "product_epsilon_right",
        "head_product",
    ),
    "TerminalProductChild": ("set_terminal_product", "child_product_a", "child_product_b", "product_epsilon_left", "product_epsilon_right"),
    "WrapOp": (
        "eager_wrap_set_equiv",
        "zipper_wrap_materialization_equiv",
        "arbitrary_zipper_wrap_set_equiv",
        "set_child_wrap_hit",
        "set_terminal_wrap",
        "wrap_unwrap_left_inverse_a",
        "wrap_unwrap_left_inverse_b",
        "wrap_unwrap_left_inverse_ab",
        "wrap_unwrap_restriction_a",
        "wrap_unwrap_restriction_b",
    ),
    "UnwrapOp": (
        "eager_unwrap_set_equiv",
        "zipper_unwrap_materialization_equiv",
        "arbitrary_zipper_unwrap_set_equiv",
        "set_child_unwrap_singleton",
        "set_terminal_unwrap",
        "wrap_unwrap_left_inverse_a",
        "wrap_unwrap_left_inverse_b",
        "wrap_unwrap_left_inverse_ab",
        "unwrap_union",
    ),
    "TailsUnionOp": (
        "eager_tails_union_set_equiv",
        "zipper_tails_union_materialization_equiv",
        "arbitrary_zipper_tails_union_set_equiv",
        "tails_union_children",
        "child_tails_union_a",
        "child_tails_union_b",
        "iteration_tail_identity",
        "tails-union-open:space_optimized_open",
    ),
    "FrontierUnionOp": (
        "frontier_union_is_tails_union",
        "tails_union_children",
        "child_tails_union_a",
        "child_tails_union_b",
    ),
    "FrontierChildUnionOp": (
        "frontier_child_union_a_after_b",
        "frontier_tail_union_a_is_child",
        "frontier_tail_union_b_is_child",
        "tails_union_children",
        "child_tails_union_a",
        "child_tails_union_b",
    ),
    "FrontierTailUnionOp": (
        "frontier_tail_union_a_is_child",
        "frontier_tail_union_b_is_child",
        "antimirov_suffix_frontier_state_child_a",
        "antimirov_suffix_frontier_state_child_b",
        "antimirov_tails_frontier_state_child_a",
        "antimirov_tails_frontier_state_child_b",
        "antimirov_suffix_frontier_state_child_fo",
        "antimirov_tails_frontier_state_child_fo",
        "tails_union_children",
        "child_tails_union_a",
        "child_tails_union_b",
        "suffix_closure_child_derivative_a",
        "suffix_closure_child_derivative_b",
        "child_tails_closure_derivative_a",
        "child_tails_closure_derivative_b",
    ),
    "FrontierStateOp": (
        "frontier_union_is_tails_union",
        "frontier_tail_union_a_is_child",
        "frontier_tail_union_b_is_child",
        "frontier_child_union_a_after_b",
        "antimirov_suffix_frontier_state_child_a",
        "antimirov_suffix_frontier_state_child_b",
        "antimirov_tails_frontier_state_child_a",
        "antimirov_tails_frontier_state_child_b",
        "antimirov_suffix_frontier_nested_a_b",
        "antimirov_tails_frontier_nested_a_b",
        "antimirov_suffix_frontier_state_child_fo",
        "antimirov_tails_frontier_state_child_fo",
        "antimirov_suffix_frontier_nested_fo",
        "antimirov_tails_frontier_nested_fo",
        "tails_union_children",
        "child_tails_union_a",
        "child_tails_union_b",
        "suffix_closure_child_derivative_a",
        "suffix_closure_child_derivative_b",
        "child_tails_closure_derivative_a",
        "child_tails_closure_derivative_b",
    ),
    "TailsIntersectionOp": (
        "eager_tails_intersection_set_equiv",
        "zipper_tails_intersection_materialization_equiv",
        "arbitrary_zipper_tails_intersection_set_equiv",
        "set_tails_intersection_closed_two_head_frontier_fo",
        "set_tails_intersection_closed_frontier_refinement_fo",
        "tails_intersection_two_known_heads",
        "tails-intersection-open:space_optimized_open",
    ),
    "PrefixClosureOp": (
        "eager_prefix_closure_set_equiv",
        "zipper_prefix_closure_materialization_equiv",
        "arbitrary_zipper_prefix_closure_set_equiv",
        "set_child_prefix_closure",
        "set_terminal_prefix_closure_empty",
        "prefix_closure_idempotent",
        "prefix-closure-open:space_optimized_open",
    ),
    "PrefixClosureBelowOp": (
        "set_child_prefix_closure_below",
        "set_terminal_prefix_closure_below",
        "set_prefix_closure_interior_terminal_fo",
        "prefix_closure_idempotent",
    ),
    "SuffixClosureOp": (
        "eager_suffix_closure_set_equiv",
        "zipper_suffix_closure_materialization_equiv",
        "arbitrary_zipper_suffix_closure_set_equiv",
        "set_child_suffix_closure_derivative",
        "antimirov_suffix_frontier_state_child_fo",
        "antimirov_suffix_frontier_nested_fo",
        "set_terminal_suffix_closure_empty",
        "suffix_closure_idempotent",
        "suffix_closure_child_derivative_a",
        "suffix_closure_child_derivative_b",
        "suffix-closure-open:space_optimized_open",
    ),
    "TailsClosureOp": (
        "eager_tails_closure_set_equiv",
        "zipper_tails_closure_materialization_equiv",
        "arbitrary_zipper_tails_closure_set_equiv",
        "set_child_tails_closure_derivative",
        "antimirov_tails_frontier_state_child_fo",
        "antimirov_tails_frontier_nested_fo",
        "antimirov_tails_frontier_nested_a_b",
        "set_tails_closure_definition_fo",
        "tails_closure_idempotent",
        "tails_closure_definition",
        "child_tails_closure_derivative_a",
        "child_tails_closure_derivative_b",
        "tails_closure_unfold_base_or_step",
        "suffix_closure_child_derivative_a",
        "suffix_closure_child_derivative_b",
        "tails-closure-open:space_optimized_open",
    ),
    "NonEmptyOp": (
        "eager_nonempty_paths_set_equiv",
        "zipper_nonempty_paths_materialization_equiv",
        "arbitrary_zipper_nonempty_paths_set_equiv",
        "set_child_nonempty_paths",
        "set_terminal_nonempty_paths_empty",
        "nonempty_empty",
        "nonempty_epsilon_empty",
        "nonempty_idempotent",
        "nonempty_subset",
        "nonempty_union",
        "nonempty_child_a",
        "nonempty_child_b",
        "iteration_reconstruct_nonempty_source",
    ),
    "RangeOp": (
        "set_range_full_sentinel",
        "set_range_empty_one_one",
        "eager_range_set_equiv",
        "zipper_range_materialization_equiv",
        "set_range_subset_fo",
        "zipper_range_full_terminal_equiv",
        "zipper_range_first_terminal_fo",
        "set_range_first_child_terminal_empty_fo",
        "set_range_first_child_selected_sound_fo",
        "set_range_first_child_pruned_fo",
        "set_range_last_child_selected_sound_fo",
        "set_range_last_child_pruned_fo",
        "set_range_drop_last_child_before_last_fo",
        "set_range_drop_last_child_after_last_fo",
        "range_empty_source_first",
        "range_empty_source_last",
        "range_empty_source_drop_last",
        "range_first_wrap_a",
        "range_last_wrap_a",
        "range_drop_last_wrap_a",
        "range_first_wrap_b",
        "range_last_wrap_b",
        "range_drop_last_wrap_b",
        "range_first_wrap_ab",
        "range_last_wrap_ab",
        "range_drop_last_wrap_ab",
        "range_first_subset",
        "range_first_idempotent",
        "range_last_idempotent",
        "range_first_of_last",
        "range_drop_last_of_first_empty",
        "range_nested_first",
        "range_nested_suffix_first",
        "range_nested_suffix_offset",
        "range_nested_last_last",
        "range_positive_same_empty",
        "range_positive_decreasing_empty",
        "range_negative_same_empty",
        "range_negative_decreasing_empty",
        "range_last_subset",
        "range_drop_last_subset",
        "range_negative_window_subset",
        "range_singleton_last_literal",
        "range_singleton_drop_last_literal",
        "range_singleton_negative_window_literal",
        "range_nested_singleton_last_literal",
        "range_item_union_first_literal",
        "range_item_union_last_literal",
        "range_item_union_drop_last_literal",
        "range_drop_last_full_sentinel_literal",
        "range_first_epsilon_literal",
        "range_first_child_border_literal",
        "range_first_child_full_literal",
        "range_prunes_after_upper_border_literal",
        "range_suffix_child_border_literal",
        "range_last_border_literal",
        "range_last_child_border_literal",
        "range_last_prunes_earlier_head_literal",
        "range_drop_last_border_literal",
        "range_drop_last_child_border_literal",
        "range_drop_last_prunes_last_head_literal",
        "range_negative_window_border_literal",
        "range_negative_window_child_border_literal",
        "range_negative_window_prunes_last_head_literal",
        "range_first_without_epsilon_literal",
        "range_first_without_epsilon_child_literal",
        "range_first_without_epsilon_prunes_later_child_literal",
    ),
    "RangeLastOp": (
        "eager_range_set_equiv",
        "zipper_range_last_materialization_equiv",
        "set_range_subset_fo",
        "set_range_last_child_selected_sound_fo",
        "set_range_last_child_pruned_fo",
        "range_empty_source_last",
        "range_last_subset",
        "range_last_idempotent",
        "range_last_wrap_a",
        "range_last_wrap_b",
        "range_last_wrap_ab",
        "range_first_of_last",
        "range_singleton_last_literal",
        "range_nested_singleton_last_literal",
        "range_item_union_last_literal",
        "range_last_border_literal",
        "range_last_child_border_literal",
        "range_last_prunes_earlier_head_literal",
        "range_negative_window_border_literal",
        "range_negative_window_child_border_literal",
        "range_negative_window_prunes_last_head_literal",
    ),
    "RangeDropLastOp": (
        "eager_range_set_equiv",
        "zipper_range_drop_last_materialization_equiv",
        "set_range_subset_fo",
        "set_range_drop_last_child_before_last_fo",
        "set_range_drop_last_child_after_last_fo",
        "range_empty_source_drop_last",
        "range_drop_last_subset",
        "range_drop_last_wrap_a",
        "range_drop_last_wrap_b",
        "range_drop_last_wrap_ab",
        "range_drop_last_of_first_empty",
        "range_singleton_drop_last_literal",
        "range_item_union_drop_last_literal",
        "range_drop_last_full_sentinel_literal",
        "range_drop_last_border_literal",
        "range_drop_last_child_border_literal",
        "range_drop_last_prunes_last_head_literal",
    ),
    "range-drop-last-child-query": (
        "eager_range_set_equiv",
        "zipper_range_drop_last_materialization_equiv",
        "set_range_subset_fo",
        "set_range_drop_last_child_before_last_fo",
        "set_range_drop_last_child_after_last_fo",
        "range_drop_last_border_literal",
        "range_drop_last_child_border_literal",
        "range_drop_last_prunes_last_head_literal",
    ),
    "RangeFirstOp": (
        "set_range_full_sentinel",
        "eager_range_set_equiv",
        "zipper_range_first_materialization_equiv",
        "set_range_subset_fo",
        "set_range_first_terminal_fo",
        "zipper_range_first_terminal_fo",
        "set_range_first_child_terminal_empty_fo",
        "set_range_first_child_selected_sound_fo",
        "set_range_first_child_pruned_fo",
        "range_empty_source_first",
        "range_first_subset",
        "range_first_wrap_a",
        "range_first_wrap_b",
        "range_first_wrap_ab",
        "range_first_idempotent",
        "range_first_of_last",
        "range_drop_last_of_first_empty",
        "range_first_epsilon_literal",
        "range_item_union_first_literal",
        "range_first_child_border_literal",
        "range_prunes_after_upper_border_literal",
        "range_first_without_epsilon_literal",
        "range_first_without_epsilon_child_literal",
        "range_first_without_epsilon_prunes_later_child_literal",
    ),
    "range-first-child-query": (
        "set_range_full_sentinel",
        "eager_range_set_equiv",
        "zipper_range_first_materialization_equiv",
        "set_range_subset_fo",
        "set_range_first_child_terminal_empty_fo",
        "set_range_first_child_selected_sound_fo",
        "set_range_first_child_pruned_fo",
        "range_first_child_border_literal",
        "range_first_without_epsilon_child_literal",
        "range_first_without_epsilon_prunes_later_child_literal",
    ),
    "range-last-child-query": (
        "eager_range_set_equiv",
        "zipper_range_last_materialization_equiv",
        "set_range_subset_fo",
        "set_range_last_child_selected_sound_fo",
        "set_range_last_child_pruned_fo",
        "range_last_border_literal",
        "range_last_child_border_literal",
        "range_last_prunes_earlier_head_literal",
    ),
    "range-child-result": (
        "eager_range_set_equiv",
        "zipper_range_materialization_equiv",
        "set_range_subset_fo",
        "set_range_first_child_terminal_empty_fo",
        "set_range_first_child_selected_sound_fo",
        "set_range_first_child_pruned_fo",
        "set_range_last_child_selected_sound_fo",
        "set_range_last_child_pruned_fo",
        "set_range_drop_last_child_before_last_fo",
        "set_range_drop_last_child_after_last_fo",
        "range_first_child_border_literal",
        "range_last_child_border_literal",
        "range_drop_last_child_border_literal",
    ),
    "iter-child-query": (
        "eager_iteration_set_equiv",
        "zipper_iteration_materialization_equiv",
        "zipper_iter_tail_materialization_equiv",
        "zipper_iter_head_materialization_equiv",
        "zipper_iter_reconstruct_materialization_equiv",
        "zipper_iter_range_tail_materialization_equiv",
        "zipper_iter_range_reconstruct_materialization_equiv",
        "zipper_iter_prefixed_range_reconstruct_materialization_equiv",
        "frontier_candidate_tail_frontier_fo",
        "zipper_base_child_equiv",
    ),
    "iter-child-result": (
        "eager_iteration_set_equiv",
        "zipper_iteration_materialization_equiv",
        "zipper_iter_tail_materialization_equiv",
        "zipper_iter_head_materialization_equiv",
        "zipper_iter_reconstruct_materialization_equiv",
        "zipper_iter_range_tail_materialization_equiv",
        "zipper_iter_range_reconstruct_materialization_equiv",
        "zipper_iter_prefixed_range_reconstruct_materialization_equiv",
        "frontier_candidate_tail_frontier_fo",
        "zipper_base_child_equiv",
    ),
    "HeadOp": (
        "eager_head_set_equiv",
        "zipper_head_materialization_equiv",
        "arbitrary_zipper_head_set_equiv",
        "set_child_head",
        "set_terminal_head_empty",
        "set_iteration_head_identity",
        "iteration_head_identity",
        "head_idempotent",
    ),
    "IterOp": (
        "eager_iteration_set_equiv",
        "zipper_iteration_materialization_equiv",
        "zipper_iter_tail_materialization_equiv",
        "zipper_iter_head_materialization_equiv",
        "zipper_iter_reconstruct_materialization_equiv",
        "zipper_iter_prefixed_reconstruct_materialization_equiv",
        "iteration_tail_identity",
        "iteration_head_identity",
        "iteration_reconstruct_nonempty_source",
        "set_iteration_prefixed_reconstruct_definition_fo",
        "iteration_prefixed_reconstruct_nonempty_source",
        "iteration_prefixed_reconstruct_two_item_nonempty_source",
        "iteration_prefixed_range_reconstruct_first_subset",
        "iteration_prefixed_range_reconstruct_first_literal",
        "iteration_prefixed_range_reconstruct_drop_last_literal",
        "iteration_prefixed_range_reconstruct_full_sentinel",
        "iteration_prefixed_range_reconstruct_empty_slice",
        "iteration_prefixed_range_reconstruct_drop_last_subset",
        "iteration_source_union_tail",
        "iteration_source_union_head",
    ),
    "BoundHeadOp": (
        "eager_iteration_set_equiv",
        "set_iteration_head_identity",
        "set_iteration_general_body_union_distribution_fo",
    ),
    "BoundTailOp": (
        "eager_iteration_set_equiv",
        "set_iteration_tail_identity",
        "set_iteration_general_body_union_distribution_fo",
    ),
    "InstantiateOp": (
        "eager_iteration_set_equiv",
        "zipper_iteration_materialization_equiv",
        "set_iteration_general_body_union_distribution_fo",
        "set_iteration_general_wrap_hoist_fo",
        "set_iteration_general_product_right_hoist_fo",
        "set_iteration_general_intersection_right_hoist_fo",
        "set_iteration_general_diff_right_hoist_fo",
        "set_iteration_general_restriction_right_hoist_fo",
    ),
    "IterBinderOp": (
        "eager_iteration_set_equiv",
        "zipper_iteration_materialization_equiv",
        "set_iteration_general_body_union_distribution_fo",
        "set_iteration_general_invariant_left_fo",
        "set_iteration_general_invariant_right_fo",
        "set_iteration_general_wrap_hoist_fo",
        "set_iteration_general_product_right_hoist_fo",
        "set_iteration_general_intersection_right_hoist_fo",
        "set_iteration_general_diff_right_hoist_fo",
        "set_iteration_general_restriction_right_hoist_fo",
    ),
    "IterBranchesOp": (
        "eager_iteration_set_equiv",
        "zipper_iteration_materialization_equiv",
        "frontier_candidate_tail_frontier_fo",
    ),
    "iter-independent": (
        "set_iteration_general_independence_structural_fo",
        "set_iteration_general_invariant_left_fo",
        "set_iteration_general_invariant_right_fo",
        "set_iteration_general_product_right_hoist_fo",
        "set_iteration_general_intersection_right_hoist_fo",
        "set_iteration_general_diff_right_hoist_fo",
        "set_iteration_general_restriction_right_hoist_fo",
    ),
    "IterRangeTailOp": (
        "set_iteration_range_tail_definition_fo",
        "zipper_iter_range_tail_materialization_equiv",
        "iteration_range_tail_full_sentinel",
        "iteration_range_tail_empty_slice",
        "iteration_range_tail_first_subset",
        "iteration_range_tail_drop_last_subset",
        "iteration_range_tail_first_literal",
        "iteration_range_tail_drop_last_literal",
        "iteration_range_tail_same_head_first_literal",
        "iteration_range_tail_same_head_drop_last_literal",
    ),
    "IterRangeReconstructOp": (
        "set_iteration_range_reconstruct_definition_fo",
        "zipper_iter_range_reconstruct_materialization_equiv",
        "iteration_range_reconstruct_full_sentinel",
        "iteration_range_reconstruct_empty_slice",
        "iteration_range_reconstruct_first_subset",
        "iteration_range_reconstruct_drop_last_subset",
        "iteration_range_reconstruct_first_literal",
        "iteration_range_reconstruct_drop_last_literal",
        "iteration_range_reconstruct_same_head_first_literal",
        "iteration_range_reconstruct_same_head_drop_last_literal",
    ),
    "IterPrefixedRangeReconstructOp": (
        "set_iteration_prefixed_range_reconstruct_definition_fo",
        "zipper_iter_prefixed_range_reconstruct_materialization_equiv",
        "iteration_prefixed_range_reconstruct_full_sentinel",
        "iteration_prefixed_range_reconstruct_empty_slice",
        "iteration_prefixed_range_reconstruct_first_subset",
        "iteration_prefixed_range_reconstruct_drop_last_subset",
        "iteration_prefixed_range_reconstruct_first_literal",
        "iteration_prefixed_range_reconstruct_drop_last_literal",
        "iteration_prefixed_range_reconstruct_same_head_drop_last_literal",
    ),
    "FixpointOp": (
        "zipper_fixpoint_tail_materialization_equiv",
        "zipper_fixpoint_head_materialization_equiv",
        "zipper_fixpoint_reconstruct_materialization_equiv",
        "zipper_fixpoint_range_tail_full_materialization_equiv",
        "zipper_fixpoint_range_tail_empty_materialization_equiv",
        "zipper_fixpoint_range_reconstruct_materialization_equiv",
        "fixpoint_tail_closure",
        "fixpoint_tail_unfold_base_or_step",
        "fixpoint_tail_unfold_via_iter_tail",
        "fixpoint_head_closure",
        "fixpoint_head_unfold_base_or_step",
        "fixpoint_reconstruct_identity",
        "fixpoint_reconstruct_unfold_base_or_step",
        "fixpoint_prefixed_reconstruct_empty_prefix_identity",
        "fixpoint_range_tail_full_sentinel_closure",
        "fixpoint_range_tail_empty_slice_identity",
        "fixpoint_range_reconstruct_full_sentinel_identity",
        "fixpoint_range_reconstruct_first_identity",
        "fixpoint_range_reconstruct_drop_last_identity",
        "fixpoint_prefixed_range_reconstruct_empty_prefix_first_identity",
        "fixpoint_prefixed_range_reconstruct_empty_prefix_drop_last_identity",
        "fixpoint-open:space_optimized_open",
    ),
    "fixpoint-child-query": (
        "zipper_fixpoint_tail_materialization_equiv",
        "zipper_fixpoint_head_materialization_equiv",
        "zipper_fixpoint_reconstruct_materialization_equiv",
        "zipper_fixpoint_range_tail_full_materialization_equiv",
        "zipper_fixpoint_range_tail_empty_materialization_equiv",
        "zipper_fixpoint_range_reconstruct_materialization_equiv",
        "fixpoint_tail_unfold_via_iter_tail",
        "zipper_base_child_equiv",
    ),
    "fixpoint-child-result": (
        "zipper_fixpoint_tail_materialization_equiv",
        "zipper_fixpoint_head_materialization_equiv",
        "zipper_fixpoint_reconstruct_materialization_equiv",
        "zipper_fixpoint_range_tail_full_materialization_equiv",
        "zipper_fixpoint_range_tail_empty_materialization_equiv",
        "zipper_fixpoint_range_reconstruct_materialization_equiv",
        "fixpoint_tail_unfold_via_iter_tail",
        "zipper_base_child_equiv",
    ),
    "fixpoint-unfold-query": (
        "zipper_fixpoint_tail_materialization_equiv",
        "zipper_fixpoint_head_materialization_equiv",
        "zipper_fixpoint_reconstruct_materialization_equiv",
        "zipper_fixpoint_range_tail_full_materialization_equiv",
        "zipper_fixpoint_range_tail_empty_materialization_equiv",
        "zipper_fixpoint_range_reconstruct_materialization_equiv",
        "fixpoint_tail_unfold_base_or_step",
        "fixpoint_head_unfold_base_or_step",
        "fixpoint_reconstruct_unfold_base_or_step",
        "fixpoint_tail_unfold_via_iter_tail",
        "eager_iteration_set_equiv",
    ),
    "fixpoint-unfold-result": (
        "zipper_fixpoint_tail_materialization_equiv",
        "zipper_fixpoint_head_materialization_equiv",
        "zipper_fixpoint_reconstruct_materialization_equiv",
        "zipper_fixpoint_range_tail_full_materialization_equiv",
        "zipper_fixpoint_range_tail_empty_materialization_equiv",
        "zipper_fixpoint_range_reconstruct_materialization_equiv",
        "fixpoint_tail_unfold_base_or_step",
        "fixpoint_head_unfold_base_or_step",
        "fixpoint_reconstruct_unfold_base_or_step",
        "fixpoint_tail_unfold_via_iter_tail",
        "eager_iteration_set_equiv",
    ),
    "Descend": (
        "zipper_base_child_equiv",
        "set_child_product_derivative",
        "set_child_restriction_derivative",
        "set_child_raffination_derivative",
        "set_child_wrap_hit",
        "set_child_unwrap_singleton",
        "set_child_head",
        "set_child_nonempty_paths",
        "set_child_prefix_closure",
        "set_child_prefix_closure_below",
        "set_child_suffix_closure_derivative",
        "set_child_tails_closure_derivative",
    ),
    "Child": (
        "zipper_base_child_equiv",
        "child_empty_a",
        "child_empty_b",
        "child_epsilon_a",
        "child_epsilon_b",
        "child_singleton_hit_a",
        "child_singleton_hit_b",
        "child_singleton_miss_a_b",
        "child_singleton_miss_b_a",
        "child_concat_hit_a",
        "child_concat_hit_b",
        "child_concat_miss_a_b",
        "child_concat_miss_b_a",
        "child_union_a",
        "child_union_b",
        "set_child_union_fo",
        "child_same_head_union_a",
        "child_same_head_union_b",
        "child_intersection_a",
        "child_intersection_b",
        "child_diff_a",
        "child_diff_b",
        "set_child_product_derivative",
        "set_child_restriction_derivative",
        "set_child_raffination_derivative",
        "set_child_wrap_hit",
        "set_child_unwrap_singleton",
        "set_child_head",
        "set_child_nonempty_paths",
        "set_child_prefix_closure",
        "set_child_prefix_closure_below",
        "set_child_suffix_closure_derivative",
        "set_child_tails_closure_derivative",
    ),
    "TrieZ": ("zipper_base_terminal_equiv", "zipper_base_child_equiv"),
    "terminal": (
        "zipper_base_terminal_equiv",
        "zipper_union_terminal_equiv",
        "zipper_intersection_terminal_equiv",
        "zipper_diff_terminal_equiv",
        "set_terminal_product",
        "set_terminal_wrap",
        "set_terminal_unwrap",
        "set_terminal_head_empty",
        "set_terminal_nonempty_paths_empty",
        "set_terminal_prefix_closure_empty",
        "set_terminal_prefix_closure_below",
        "set_terminal_suffix_closure_empty",
    ),
    "PatchChildOp": (
        "zipper_patch_child_terminal_equiv",
        "zipper_patch_child_hit_equiv",
        "zipper_patch_child_miss_equiv",
        "zipper_patch_child_identity_equiv",
        "zipper_context_graft_materialization",
        "patch_child_hit_a",
        "patch_child_hit_b",
        "patch_child_miss_b",
        "patch_child_miss_a",
        "patch_child_identity_a",
        "patch_child_identity_b",
        "patch_child_terminal_preserved",
        "patch_child_materialization_a",
    ),
    "tail-frontier": (
        "frontier_tail_nonempty_has_key_fo",
        "frontier_candidate_tail_frontier_fo",
        "set_child_union_fo",
        "child_same_head_union_a",
        "child_same_head_union_b",
        "child_union_a",
        "child_union_b",
        "child_intersection_a",
        "child_intersection_b",
        "child_diff_a",
        "child_diff_b",
        "child_restriction_a",
        "child_restriction_b",
        "child_product_a",
        "child_product_b",
        "suffix_closure_child_derivative_a",
        "suffix_closure_child_derivative_b",
    ),
    "suffix-active": (
        "set_child_suffix_closure_derivative",
        "suffix_closure_child_derivative_a",
        "suffix_closure_child_derivative_b",
    ),
    "frontier-candidate": (
        "frontier_candidate_has_key_fo",
        "frontier_candidate_tail_frontier_fo",
        "tails_union_children",
    ),
    "frontier-union1-query": (
        "frontier_union_is_tails_union",
        "frontier_candidate_has_key_fo",
        "frontier_candidate_tail_frontier_fo",
        "tails_union_children",
        "antimirov_suffix_frontier_state_child_fo",
        "antimirov_tails_frontier_state_child_fo",
    ),
    "frontier-union2-query": (
        "frontier_union_is_tails_union",
        "frontier_candidate_has_key_fo",
        "frontier_candidate_tail_frontier_fo",
        "tails_union_children",
        "child_tails_union_a",
        "child_tails_union_b",
    ),
    "frontier-union-result": (
        "frontier_union_is_tails_union",
        "frontier_candidate_has_key_fo",
        "frontier_candidate_tail_frontier_fo",
        "tails_union_children",
        "child_tails_union_a",
        "child_tails_union_b",
        "antimirov_suffix_frontier_state_child_fo",
        "antimirov_tails_frontier_state_child_fo",
    ),
    "plugged": (
        "zipper_context_root_plug_equiv",
        "zipper_context_down_plug_invariance",
        "zipper_context_graft_materialization",
        "zipper_context_cursor_source_plug",
    ),
    "cursor": (
        "zipper_context_root_plug_equiv",
        "zipper_context_down_plug_invariance",
        "zipper_context_up_after_down_context",
        "zipper_context_up_after_down_focus",
        "zipper_context_cursor_source_plug",
    ),
    "down-move": (
        "zipper_context_down_plug_invariance",
        "zipper_context_up_after_down_context",
        "zipper_context_up_after_down_focus",
        "zipper_context_graft_materialization",
    ),
    "up-move": (
        "zipper_context_up_after_down_context",
        "zipper_context_up_after_down_focus",
        "zipper_context_graft_materialization",
    ),
    "next-sibling-move": (
        "zipper_context_sibling_path",
        "zipper_context_sibling_target_context",
        "zipper_context_sibling_target_focus",
        "zipper_context_sibling_target_path",
        "zipper_context_sibling_target_plug_invariance",
        "zipper_context_sibling_plug_invariance",
    ),
    "previous-sibling-move": (
        "zipper_context_sibling_path",
        "zipper_context_sibling_target_context",
        "zipper_context_sibling_target_focus",
        "zipper_context_sibling_target_path",
        "zipper_context_sibling_target_plug_invariance",
        "zipper_context_sibling_plug_invariance",
    ),
    "next-sibling-target": (
        "zipper_context_sibling_path",
        "zipper_context_sibling_target_context",
        "zipper_context_sibling_target_focus",
        "zipper_context_sibling_target_path",
        "zipper_context_sibling_target_plug_invariance",
        "zipper_context_sibling_plug_invariance",
    ),
    "previous-sibling-target": (
        "zipper_context_sibling_path",
        "zipper_context_sibling_target_context",
        "zipper_context_sibling_target_focus",
        "zipper_context_sibling_target_path",
        "zipper_context_sibling_target_plug_invariance",
        "zipper_context_sibling_plug_invariance",
    ),
    "adjacent-before": (
        "zipper_context_sibling_path",
        "zipper_context_sibling_target_context",
        "zipper_context_sibling_target_focus",
        "zipper_context_sibling_target_path",
        "zipper_context_sibling_target_plug_invariance",
        "zipper_context_sibling_plug_invariance",
    ),
    "context-path": (
        "zipper_context_root_path",
        "zipper_context_down_path",
        "zipper_context_up_after_down_path",
    ),
    "cursor-path": (
        "zipper_context_root_path",
        "zipper_context_down_path",
        "zipper_context_up_after_down_path",
    ),
}


TOKEN_OPERATION_NAMES = frozenset({
    "Descend",
    "Child",
    "TrieZ",
    "EmptyZ",
    "MemoZ",
    "terminal",
    "empty-focus",
    "nonterminal",
    "nonempty-focus",
    "has-key",
    "observed-key",
    "observable-focus",
    "child-focus",
    "absent-key",
    "keyset",
    "single-frontier",
    "KUnion",
    "KIntersection",
    "KDiff",
    "next-sibling-target",
    "previous-sibling-target",
    "adjacent-before",
    "ordered-before",
    "needs-first-head",
    "needs-last-head",
    "first-head",
    "last-head",
    "range-first-child-query",
    "range-last-child-query",
    "range-drop-last-child-query",
    "range-child-result",
    "iter-child-query",
    "iter-child-result",
    "fixpoint-child-query",
    "fixpoint-child-result",
    "fixpoint-unfold-query",
    "fixpoint-unfold-result",
    "frontier-union1-query",
    "frontier-union2-query",
    "frontier-union-result",
})

RELATIONAL_ANALYSIS_OPERATIONS = frozenset({
    "EmptyZ",
    "MemoZ",
    "empty-focus",
    "nonterminal",
    "nonempty-focus",
    "has-key",
    "observed-key",
    "observable-focus",
    "absent-key",
    "keyset",
    "single-frontier",
    "KUnion",
    "KIntersection",
    "KDiff",
    "next-sibling-target",
    "previous-sibling-target",
    "adjacent-before",
    "ordered-before",
    "needs-first-head",
    "needs-last-head",
    "first-head",
    "last-head",
    "range-first-child-query",
    "range-last-child-query",
    "range-drop-last-child-query",
    "range-child-result",
    "iter-child-query",
    "iter-child-result",
    "fixpoint-child-query",
    "fixpoint-child-result",
    "fixpoint-unfold-query",
    "fixpoint-unfold-result",
    "frontier-union1-query",
    "frontier-union2-query",
    "frontier-union-result",
})

FRONTIER_SCHEDULE_ANALYSIS_OPERATIONS = frozenset({
    "keyset",
    "observed-key",
    "observable-focus",
    "child-focus",
    "absent-key",
})

MEMO_HELPER_OPERATIONS = frozenset({"MemoZ"})

PATH_NORMALIZER_ARTIFACTS = (
    "path_concat_epsilon_left_fo",
    "path_concat_epsilon_right_fo",
)

CONCRETE_KEYSET_OPERATIONS = frozenset({"EmptyZ", "TrieZ", "keyset"})

CONCRETE_KEYSET_ARTIFACTS = (
    "zipper_keyset_emptyz_fo",
    "zipper_keyset_trie_empty_fo",
    "zipper_keyset_trie_epsilon_fo",
    "zipper_keyset_trie_item_fo",
    "zipper_keyset_trie_concat_fo",
)

CONTEXT_PROOF_OPERATIONS = frozenset({
    "PatchChildOp",
    "plugged",
    "cursor",
    "down-move",
    "up-move",
    "next-sibling-move",
    "previous-sibling-move",
    "next-sibling-target",
    "previous-sibling-target",
    "context-path",
    "cursor-path",
})


OPERATION_TOKEN_RE_CACHE: dict[str, re.Pattern[str]] = {}


def operation_in_text(op: str, text: str) -> bool:
    pattern = OPERATION_TOKEN_RE_CACHE.get(op)
    if pattern is None:
        pattern = re.compile(rf"(?<![A-Za-z0-9_-]){re.escape(op)}(?![A-Za-z0-9_-])")
        OPERATION_TOKEN_RE_CACHE[op] = pattern
    return pattern.search(text) is not None


UNBOUNDED_ARTIFACT_PREFIXES = (
    "zipper_",
    "eager_",
    "set_",
    "arbitrary_",
)


def collect_egg_rules(path: Path) -> list[tuple[str, int, str]]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    rules: list[tuple[str, int, str]] = []
    i = 0
    while i < len(lines):
        stripped = lines[i].lstrip()
        if stripped.startswith("(rewrite ") or stripped.startswith("(rule "):
            start = i
            buf = [lines[i]]
            balance = lines[i].count("(") - lines[i].count(")")
            i += 1
            while balance > 0 and i < len(lines):
                buf.append(lines[i])
                balance += lines[i].count("(") - lines[i].count(")")
                i += 1
            kind = "rewrite" if stripped.startswith("(rewrite ") else "rule"
            rules.append((kind, start + 1, "\n".join(buf)))
        else:
            i += 1
    return rules


def strongest_artifact_kind(kinds: set[str]) -> str:
    if "vampire" in kinds:
        return "vampire"
    if "z3" in kinds:
        return "z3"
    if "egg" in kinds:
        return "egg"
    return "unknown"


def operational_rule_status(operations: tuple[str, ...], artifacts_by_name: dict[str, set[str]]) -> tuple[str, str, tuple[str, ...], str]:
    def hinted_artifacts() -> list[str]:
        hinted: list[str] = []
        for op in operations:
            for name in OPERATION_ARTIFACT_HINTS.get(op, ()):
                if name in artifacts_by_name and name not in hinted:
                    hinted.append(name)
        return hinted

    def status_from_hints(hinted: list[str]) -> tuple[str, str, tuple[str, ...], str]:
        strongest = {strongest_artifact_kind(artifacts_by_name[name]) for name in hinted}
        has_unbounded = "vampire" in strongest
        has_bounded = bool(strongest & {"z3", "egg"})
        if has_unbounded and not has_bounded:
            return "FOL", "proved-unbounded", tuple(hinted), "mapped to first-order proof artifact(s)"
        if has_unbounded and has_bounded:
            return "mixed", "proved-bounded", tuple(hinted), "mixed FOL plus bounded evidence; weakest proof tier is bounded"
        return "bounded", "proved-bounded", tuple(hinted), "mapped to bounded SMT/egg proof artifact(s)"

    hinted = hinted_artifacts()
    op_set = set(operations)
    exact_helper_artifacts: tuple[str, ...] = ()
    if "InstantiateOp" in op_set:
        exact_helper_artifacts = (
            "eager_iteration_set_equiv",
            "set_iteration_general_body_union_distribution_fo",
            "set_iteration_general_wrap_hoist_fo",
            "set_iteration_general_product_right_hoist_fo",
            "set_iteration_general_intersection_right_hoist_fo",
            "set_iteration_general_diff_right_hoist_fo",
            "set_iteration_general_restriction_right_hoist_fo",
        )
    elif "IterBinderOp" in op_set:
        exact_helper_artifacts = (
            "eager_iteration_set_equiv",
            "zipper_iteration_materialization_equiv",
            "set_iteration_general_body_union_distribution_fo",
            "set_iteration_general_invariant_left_fo",
            "set_iteration_general_invariant_right_fo",
            "set_iteration_general_wrap_hoist_fo",
            "set_iteration_general_product_right_hoist_fo",
            "set_iteration_general_intersection_right_hoist_fo",
            "set_iteration_general_diff_right_hoist_fo",
            "set_iteration_general_restriction_right_hoist_fo",
        )
    elif "IterBranchesOp" in op_set:
        exact_helper_artifacts = (
            "eager_iteration_set_equiv",
            "zipper_iteration_materialization_equiv",
            "frontier_candidate_tail_frontier_fo",
        )
    elif "iter-independent" in op_set:
        exact_helper_artifacts = ("set_iteration_general_independence_structural_fo",)
    elif {"TailsIntersectionOp", "single-frontier"} <= op_set:
        exact_helper_artifacts = ("set_tails_intersection_closed_two_head_frontier_fo",)
    elif op_set == {"PrefixClosureBelowOp", "nonempty-focus", "terminal"}:
        exact_helper_artifacts = ("set_prefix_closure_interior_terminal_fo",)
    elif op_set == {"ordered-before"}:
        exact_helper_artifacts = ("ordered_before_transitive_fo",)
    elif op_set == {"has-key", "keyset"}:
        exact_helper_artifacts = ("has_key_keyset_singleton_fo",)
    elif op_set == {"Child", "observed-key", "observable-focus", "child-focus"}:
        exact_helper_artifacts = ("child_focus_child_fo",)
    elif op_set == {"empty-focus", "child-focus", "absent-key"}:
        exact_helper_artifacts = ("child_focus_empty_absent_key_fo",)
    elif op_set == {"nonempty-focus", "has-key", "observed-key"}:
        exact_helper_artifacts = ("scheduler_has_key_observes_fo",)
    elif op_set == {"tail-frontier", "observed-key", "observable-focus"}:
        exact_helper_artifacts = ("scheduler_tail_frontier_observes_fo",)
    elif op_set == {"frontier-candidate", "keyset"}:
        exact_helper_artifacts = ("frontier_candidate_keyset_fo",)
    elif op_set == {"FrontierStateOp", "frontier-candidate", "keyset"}:
        exact_helper_artifacts = ("frontier_state_candidate_keyset_fo",)
    elif op_set == {"TailsIntersectionOp", "keyset", "single-frontier"}:
        exact_helper_artifacts = ("tails_intersection_single_frontier_keyset_fo",)
    if exact_helper_artifacts and all(name in artifacts_by_name for name in exact_helper_artifacts):
        return status_from_hints(list(exact_helper_artifacts))
    if MEMO_HELPER_OPERATIONS & set(operations):
        if hinted:
            return status_from_hints(hinted)
        return "egg-analysis", "axiom-elsewhere", ("zipper-descend.egg",), "memo/cache helper axiom checked by egglog; semantic rows are covered through the wrapped operation"
    if CONTEXT_PROOF_OPERATIONS & set(operations):
        if hinted:
            return status_from_hints(hinted)
        return "work-queue", "UNPROVED", (), "context/patch movement still needs FO plug/up/graft laws"
    if "keyset" in operations and set(operations) <= CONCRETE_KEYSET_OPERATIONS:
        concrete_keyset = [name for name in CONCRETE_KEYSET_ARTIFACTS if name in artifacts_by_name]
        if concrete_keyset:
            return status_from_hints(concrete_keyset)
    if FRONTIER_SCHEDULE_ANALYSIS_OPERATIONS & set(operations):
        return "egg-analysis", "axiom-elsewhere", ("zipper-descend.egg",), "frontier/key scheduling helper checked by egglog probes; exact frontier soundness rows are covered by FOL artifacts"
    if hinted:
        return status_from_hints(hinted)
    if RELATIONAL_ANALYSIS_OPERATIONS & set(operations):
        return "egg-analysis", "axiom-elsewhere", ("zipper-descend.egg",), "relational analysis/helper axiom checked by egglog probes and kept out of equality rewrites"
    if not operations:
        if all(name in artifacts_by_name for name in PATH_NORMALIZER_ARTIFACTS):
            return status_from_hints(list(PATH_NORMALIZER_ARTIFACTS))
        return "egg-normalizer", "axiom-elsewhere", ("zipper-descend.egg",), "path normalizer axiom checked by egglog"
    if any(op in {"PatchChildOp", "plugged", "cursor", "down-move", "up-move", "next-sibling-move", "previous-sibling-move"} for op in operations):
        return "work-queue", "UNPROVED", (), "context/patch movement still needs FO plug/up/graft laws"
    return "work-queue", "UNPROVED", (), "no matching proof artifact yet"


def generate_operational_rule_manifest(root: Path, artifacts: list[Artifact], output: Path) -> Result:
    source = root / "zipper-descend.egg"
    if not source.exists():
        return Result("operational rule manifest generation", "exit-0", "missing-source", False, output, "zipper-descend.egg not found")
    artifacts_by_name: dict[str, set[str]] = {}
    for artifact in artifacts:
        artifacts_by_name.setdefault(artifact.name, set()).add(artifact.kind)
    rows: list[OperationalRule] = []
    for idx, (kind, line, text) in enumerate(collect_egg_rules(source), start=1):
        operations = tuple(op for op in OPERATION_NAMES if operation_in_text(op, text))
        tier, status, linked, note = operational_rule_status(operations, artifacts_by_name)
        rows.append(OperationalRule(
            rule_id=f"zipper-descend:{idx:04d}",
            kind=kind,
            line=line,
            operations=operations,
            tier=tier,
            status=status,
            artifacts=linked,
            note=note,
            rule=" ".join(part.strip() for part in text.splitlines() if part.strip()),
        ))
    output.parent.mkdir(parents=True, exist_ok=True)
    header = ["rule_id", "kind", "line", "operations", "tier", "status", "artifacts", "note", "rule"]
    body = [
        "\t".join([
            manifest_escape(row.rule_id),
            manifest_escape(row.kind),
            str(row.line),
            manifest_escape(",".join(row.operations)),
            manifest_escape(row.tier),
            manifest_escape(row.status),
            manifest_escape(",".join(row.artifacts)),
            manifest_escape(row.note),
            manifest_escape(row.rule),
        ])
        for row in rows
    ]
    output.write_text("\t".join(header) + "\n" + "\n".join(body) + "\n", encoding="utf-8")
    unproved = sum(1 for row in rows if row.status == "UNPROVED")
    note = f"{len(rows)} operational rules, {unproved} UNPROVED rows"
    return Result("operational rule manifest generation", "exit-0", "exit-0", True, output, note)


def read_operational_manifest(path: Path) -> list[OperationalRule]:
    if not path.exists():
        return []
    lines = [line for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    if not lines:
        return []
    header = lines[0].split("\t")
    expected_header = ["rule_id", "kind", "line", "operations", "tier", "status", "artifacts", "note", "rule"]
    if header != expected_header:
        raise RuntimeError(f"bad operational manifest header in {path}: {header}")
    rows: list[OperationalRule] = []
    for line in lines[1:]:
        parts = [manifest_unescape(part) for part in line.split("\t")]
        if len(parts) != 9:
            raise RuntimeError(f"bad operational manifest row in {path}: {line}")
        rows.append(OperationalRule(
            rule_id=parts[0],
            kind=parts[1],
            line=int(parts[2]),
            operations=tuple(op for op in parts[3].split(",") if op),
            tier=parts[4],
            status=parts[5],
            artifacts=tuple(artifact for artifact in parts[6].split(",") if artifact),
            note=parts[7],
            rule=parts[8],
        ))
    return rows


def operational_manifest_stats(rows: list[OperationalRule]) -> OperationalManifestStats:
    return OperationalManifestStats(
        total=len(rows),
        proved_unbounded=sum(1 for row in rows if row.status == "proved-unbounded"),
        proved_bounded=sum(1 for row in rows if row.status == "proved-bounded"),
        axiom_elsewhere=sum(1 for row in rows if row.status == "axiom-elsewhere"),
        unproved=sum(1 for row in rows if row.status == "UNPROVED"),
        mixed_bounded=sum(1 for row in rows if row.status == "proved-bounded" and row.tier == "mixed"),
        bounded_only=sum(1 for row in rows if row.status == "proved-bounded" and row.tier == "bounded"),
    )


def validate_operational_manifest_closed(path: Path) -> Result:
    rows = read_operational_manifest(path)
    if not rows:
        return Result(
            "operational manifest closure and proof-debt accounting",
            "0-UNPROVED with proof-debt surfaced",
            "missing-or-empty",
            False,
            path,
            "operational manifest is missing or empty",
        )
    stats = operational_manifest_stats(rows)
    unproved = [row for row in rows if row.status == "UNPROVED"]
    if unproved:
        examples = "; ".join(
            f"{row.rule_id}@{row.line}:{','.join(row.operations) or '<no-op>'}"
            for row in unproved[:8]
        )
        suffix = "" if len(unproved) <= 8 else f"; +{len(unproved) - 8} more"
        return Result(
            "operational manifest closure and proof-debt accounting",
            "0-UNPROVED with proof-debt surfaced",
            f"{stats.unproved}-UNPROVED; {stats.proof_debt}-proof-debt",
            False,
            path,
            f"unproved operational rows remain: {examples}{suffix}",
        )
    return Result(
        "operational manifest closure and proof-debt accounting",
        "0-UNPROVED with proof-debt surfaced",
        f"0-UNPROVED; {stats.proof_debt}-proof-debt",
        True,
        path,
        (
            f"{stats.total} operational rules: {stats.proved_unbounded} proved-unbounded, "
            f"{stats.proved_bounded} proved-bounded ({stats.mixed_bounded} mixed, {stats.bounded_only} bounded-only), "
            f"{stats.axiom_elsewhere} axiom-elsewhere"
        ),
    )


def validate_no_concrete_closure_rewrites(root: Path) -> Result:
    sources = [root / "zipper-descend.egg"]
    tests_dir = root / "zipper-egg-tests"
    if tests_dir.exists():
        sources.extend(sorted(tests_dir.glob("*.egg")))
    violations: list[tuple[Path, int, str]] = []
    missing = [source for source in sources if not source.exists()]
    for source in sources:
        if not source.exists():
            continue
        for kind, line, text in collect_egg_rules(source):
            if kind != "rewrite":
                continue
            if "(TrieZ" not in text:
                continue
            if "SuffixClosureOp" in text or "TailsClosureOp" in text:
                violations.append((source, line, " ".join(part.strip() for part in text.splitlines() if part.strip())))
    if missing:
        return Result(
            "concrete closure rewrite invariant",
            "no-concrete-closure-rewrites",
            "missing-source",
            False,
            root / "zipper-descend.egg",
            "missing egg source(s): " + ", ".join(display_path(root, path) for path in missing),
        )
    if violations:
        examples = "; ".join(
            f"{display_path(root, source)}:{line}:{text}"
            for source, line, text in violations[:5]
        )
        suffix = "" if len(violations) <= 5 else f"; +{len(violations) - 5} more"
        return Result(
            "concrete closure rewrite invariant",
            "no-concrete-closure-rewrites",
            f"{len(violations)} violation(s)",
            False,
            root / "zipper-descend.egg",
            f"closure rewrites must stay frontier/state based, not concrete TrieZ expansion: {examples}{suffix}",
        )
    return Result(
        "concrete closure rewrite invariant",
        "no-concrete-closure-rewrites",
        "ok",
        True,
        root / "zipper-descend.egg",
        f"scanned {len(sources)} egg file(s); no SuffixClosureOp/TailsClosureOp rewrite over TrieZ",
    )


def validate_frontier_algebra_rules(root: Path) -> Result:
    sources = [
        root / "zipper-descend.egg",
        root / "zipper-egg-tests" / "frontier-antimirov.egg",
    ]
    missing_sources = [source for source in sources if not source.exists()]
    if missing_sources:
        return Result(
            "frontier algebra rule invariant",
            "required-tail-frontier-and-state-rules",
            "missing-source",
            False,
            root / "zipper-descend.egg",
            "missing frontier algebra source(s): "
            + ", ".join(display_path(path, root) for path in missing_sources),
        )

    requirements: list[tuple[str, tuple[str, ...]]] = [
        (
            "intersection joins shared-key frontiers",
            (
                "(= src (IntersectionOp a b))",
                "(tail-frontier a item left-tail)",
                "(tail-frontier b item right-tail)",
                "(tail-frontier src item (IntersectionOp left-tail right-tail))",
            ),
        ),
        (
            "diff is left-guided with rhs child subtraction",
            (
                "(= src (DiffOp a b))",
                "(tail-frontier a item tail)",
                "(tail-frontier src item (DiffOp tail (Child item b)))",
            ),
        ),
        (
            "restriction terminal-prefix case descends source directly",
            (
                "(= src (RestrictionOp source prefixes))",
                "(terminal prefixes)",
                "(tail-frontier source item tail)",
                "(tail-frontier src item tail)",
            ),
        ),
        (
            "restriction nonterminal-prefix case keeps matching prefix tail",
            (
                "(= src (RestrictionOp source prefixes))",
                "(nonterminal prefixes)",
                "(tail-frontier source item source-tail)",
                "(tail-frontier prefixes item prefix-tail)",
                "(tail-frontier src item (RestrictionOp source-tail prefix-tail))",
            ),
        ),
        (
            "concat left frontier appends right",
            (
                "(= src (ConcatOp left right))",
                "(tail-frontier left item left-tail)",
                "(tail-frontier src item (ConcatOp left-tail right))",
            ),
        ),
        (
            "concat terminal-left also exposes right frontier",
            (
                "(= src (ConcatOp left right))",
                "(terminal left)",
                "(tail-frontier right item right-tail)",
                "(tail-frontier src item right-tail)",
            ),
        ),
        (
            "wrap epsilon delegates frontier",
            (
                "(= src (WrapOp z (Eps)))",
                "(tail-frontier z item tail)",
                "(tail-frontier src item tail)",
            ),
        ),
        (
            "wrap single item exposes wrapped source",
            (
                "(= src (WrapOp z (Item item)))",
                "(tail-frontier src item z)",
            ),
        ),
        (
            "wrap deep prefix exposes residual wrapper",
            (
                "(= src (WrapOp z (Concat (Item item) rest)))",
                "(tail-frontier src item (WrapOp z rest))",
            ),
        ),
        (
            "suffix closure seeds active frontier",
            (
                "(= closure (SuffixClosureOp root))",
                "(suffix-active root root)",
            ),
        ),
        (
            "tails closure seeds active frontier",
            (
                "(= closure (TailsClosureOp root))",
                "(suffix-active root root)",
            ),
        ),
        (
            "closure frontier advances active state",
            (
                "(suffix-active root active)",
                "(tail-frontier active head tail)",
                "(suffix-active root tail)",
            ),
        ),
        (
            "suffix closure exposes active tail frontiers",
            (
                "(= src (SuffixClosureOp root))",
                "(suffix-active root active)",
                "(tail-frontier active item tail)",
                "(tail-frontier src item tail)",
            ),
        ),
        (
            "tails closure exposes active tail frontiers",
            (
                "(= src (TailsClosureOp root))",
                "(suffix-active root active)",
                "(tail-frontier active item tail)",
                "(tail-frontier src item tail)",
            ),
        ),
        (
            "frontier state descends by transforming active frontier set",
            (
                "(Child item (FrontierStateOp active))",
                "(FrontierStateOp (FrontierChildUnionOp active item))",
            ),
        ),
        (
            "frontier tail union enumerates matching tails",
            (
                "(FrontierTailUnionOp src item)",
                "(tail-frontier src item tail)",
                "(frontier-candidate",
                "tail)",
            ),
        ),
        (
            "frontier-state one-tail reification",
            (
                "(frontier-union1-query z active candidate)",
                "(frontier-candidate active candidate)",
                "(frontier-union-result z candidate)",
            ),
        ),
        (
            "frontier-state two-tail union reification",
            (
                "(frontier-union2-query z active left right)",
                "(frontier-candidate active left)",
                "(frontier-candidate active right)",
                "(frontier-union-result z (UnionOp left right))",
            ),
        ),
    ]

    missing_by_source: list[tuple[Path, list[str]]] = []
    for source in sources:
        text = source.read_text(encoding="utf-8")
        missing = [
            name
            for name, needles in requirements
            if not all(needle in text for needle in needles)
        ]
        if missing:
            missing_by_source.append((source, missing))
    if missing_by_source:
        details = "; ".join(
            f"{display_path(source, root)} missing {', '.join(missing)}"
            for source, missing in missing_by_source
        )
        return Result(
            "frontier algebra rule invariant",
            "required-tail-frontier-and-state-rules",
            "missing-rules",
            False,
            root / "zipper-descend.egg",
            "missing required frontier algebra structure: " + details,
        )
    return Result(
        "frontier algebra rule invariant",
        "required-tail-frontier-and-state-rules",
        "ok",
        True,
        root / "zipper-descend.egg",
        f"{len(requirements)} required frontier algebra rule shapes present in {len(sources)} egg files",
    )


def validate_iter_fixpoint_acceptance(artifacts: list[Artifact], root: Path) -> Result:
    sources = [
        root / "zipper-descend.egg",
        root / "zipper-egg-tests" / "iter-fixpoint.egg",
        root / "zipper-egg-tests" / "datalog-semi-naive.egg",
    ]
    missing_sources = [source for source in sources if not source.exists()]
    errors: list[str] = []
    if missing_sources:
        errors.append(
            "missing egg source(s): "
            + ", ".join(display_path(source, root) for source in missing_sources)
        )

    by_name = {artifact.name: artifact for artifact in artifacts}
    required_artifacts = {
        "zipper_iteration_materialization_equiv": ("vampire", "Theorem"),
        "zipper_iter_tail_materialization_equiv": ("vampire", "Theorem"),
        "zipper_iter_head_materialization_equiv": ("vampire", "Theorem"),
        "zipper_iter_reconstruct_materialization_equiv": ("vampire", "Theorem"),
        "zipper_fixpoint_tail_materialization_equiv": ("vampire", "Theorem"),
        "zipper_fixpoint_head_materialization_equiv": ("vampire", "Theorem"),
        "zipper_fixpoint_reconstruct_materialization_equiv": ("vampire", "Theorem"),
        "semi-naive-datalog-full-program:structural_backend_equivalence": ("vampire", "Theorem"),
    }
    for name, (kind, expected) in required_artifacts.items():
        artifact = by_name.get(name)
        if artifact is None:
            errors.append(f"missing manifest artifact `{name}`")
            continue
        if artifact.kind != kind or artifact.expected != expected:
            errors.append(f"{name} must be {kind}/{expected}, got {artifact.kind}/{artifact.expected}")
        if not artifact.artifact.exists():
            errors.append(f"{name} artifact missing at {display_path(artifact.artifact, root)}")
    structural = by_name.get("semi-naive-datalog-full-program:structural_backend_equivalence")
    if structural is not None and "zipper" not in structural.note.lower():
        errors.append("semi-naive structural backend manifest note must explicitly mention the zipper tier")

    def check_needles(source: Path, label: str, needles: tuple[str, ...]) -> None:
        if not source.exists():
            return
        text = source.read_text(encoding="utf-8")
        missing = [needle for needle in needles if needle not in text]
        if missing:
            errors.append(
                f"{display_path(source, root)} missing {label}: "
                + ", ".join(f"`{needle}`" for needle in missing[:5])
                + ("" if len(missing) <= 5 else f", +{len(missing) - 5} more")
            )

    binary_needles = (
        "(IterZ Zipper IterTemplate)",
        "(FixpointZ Zipper IterTemplate)",
        "(IterOp Zipper IterTemplate)",
        "(FixpointOp Zipper IterTemplate)",
        "(rewrite (IterZ z template) (IterOp z template))",
        "(rewrite (FixpointZ z template) (FixpointOp z template))",
    )
    for source in (root / "zipper-descend.egg", root / "zipper-egg-tests" / "iter-fixpoint.egg"):
        check_needles(source, "binary IterZ/FixpointZ syntax", binary_needles)

    zipper_descend = root / "zipper-descend.egg"
    check_needles(
        zipper_descend,
        "direct Iter/Fixpoint child movement",
        (
            "(Child item (IterOp src (TailTemplate)))",
            "(FrontierChildUnionOp (FrontierUnionOp src) item)",
            "(Child item (IterOp src (HeadTemplate)))",
            "(Child item (HeadOp src))",
            "(Child item (IterOp src (ReconstructTemplate)))",
            "(Child item (NonEmptyOp src))",
            "(Child item (FixpointOp src (TailTemplate)))",
            "(FrontierStateOp (FrontierTailUnionOp (TailsClosureOp src) item))",
            "(Child item (FixpointOp src (HeadTemplate)))",
            "(Child item (UnionOp src (HeadOp src)))",
            "(Child item (FixpointOp src (ReconstructTemplate)))",
            "(Child item src)",
        ),
    )
    check_needles(
        zipper_descend,
        "Kleene fixpoint unfold witnesses",
        (
            "(fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (TailTemplate)) (TailTemplate))))",
            "(fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (HeadTemplate)) (HeadTemplate))))",
            "(fixpoint-unfold-result z (UnionOp src (IterOp (FixpointOp src (ReconstructTemplate)) (ReconstructTemplate))))",
        ),
    )

    datalog = root / "zipper-egg-tests" / "datalog-semi-naive.egg"
    check_needles(
        datalog,
        "semi-naive datalog IterZ witness",
        (
            "$datalog_semi_naive_semi_naive_complete_path_projection",
            "(IterZ $datalog_semi_naive_semi_naive_complete_path_projection (ReconstructTemplate))",
            "$datalog_semi_naive_semi_naive_iter_program",
            "$datalog_semi_naive_semi_naive_iter_whole_path_n0_n5_focus",
            "$datalog_semi_naive_semi_naive_projected_whole_path_n0_n5_focus",
            "(check (= $datalog_semi_naive_semi_naive_iter_whole_path_n0_n5_focus $datalog_semi_naive_semi_naive_projected_whole_path_n0_n5_focus))",
            "__semi_naive_absent_tail",
            "semi_naive_datalog_full_program_structural_backend_equivalence.p",
        ),
    )
    if datalog.exists():
        text = datalog.read_text(encoding="utf-8")
        direct_iter_child_checks = text.count("(check (= $datalog_semi_naive_semi_naive_iter_child_")
        if direct_iter_child_checks < 5:
            errors.append(
                "datalog IterZ witness must include direct operational child checks for at least five heads, "
                f"found {direct_iter_child_checks}"
            )
        if "(IterZ $datalog_semi_naive_scala_result_zipper (ReconstructTemplate))" in text:
            errors.append("datalog IterZ witness regressed to the already-materialized scala result zipper")

    if errors:
        return Result(
            "iter/fixpoint acceptance invariant",
            "binary-iter-fixpoint+datalog-zipper-tier",
            "invalid",
            False,
            root / "zipper-descend.egg",
            "; ".join(errors),
        )
    return Result(
        "iter/fixpoint acceptance invariant",
        "binary-iter-fixpoint+datalog-zipper-tier",
        "ok",
        True,
        root / "zipper-descend.egg",
        "binary IterZ/FixpointZ, direct child movement, Kleene unfold witnesses, datalog IterZ projection, and zipper-tier FOL artifacts are present",
    )


def validate_context_movement_acceptance(artifacts: list[Artifact], root: Path) -> Result:
    sources = [
        root / "zipper-descend.egg",
        root / "zipper-egg-tests" / "context-movement.egg",
        root / "src" / "test" / "scala" / "ZipperEggContextMovementProgram.scala",
    ]
    missing_sources = [source for source in sources if not source.exists()]
    errors: list[str] = []
    if missing_sources:
        errors.append(
            "missing context movement source(s): "
            + ", ".join(display_path(source, root) for source in missing_sources)
        )

    by_name = {artifact.name: artifact for artifact in artifacts}
    required_artifacts = {
        "zipper_context_root_plug_equiv",
        "zipper_context_down_plug_invariance",
        "zipper_context_up_after_down_context",
        "zipper_context_up_after_down_focus",
        "zipper_context_graft_materialization",
        "zipper_context_cursor_source_plug",
        "zipper_context_root_path",
        "zipper_context_down_path",
        "zipper_context_up_after_down_path",
        "zipper_context_sibling_path",
        "zipper_context_sibling_target_context",
        "zipper_context_sibling_target_focus",
        "zipper_context_sibling_target_path",
        "zipper_context_sibling_target_plug_invariance",
        "zipper_context_sibling_plug_invariance",
    }
    for name in sorted(required_artifacts):
        artifact = by_name.get(name)
        if artifact is None:
            errors.append(f"missing manifest artifact `{name}`")
            continue
        if artifact.kind != "vampire" or artifact.expected != "Theorem":
            errors.append(f"{name} must be vampire/Theorem, got {artifact.kind}/{artifact.expected}")
        if not artifact.artifact.exists():
            errors.append(f"{name} artifact missing at {display_path(artifact.artifact, root)}")

    def check_needles(source: Path, label: str, needles: tuple[str, ...]) -> None:
        if not source.exists():
            return
        text = source.read_text(encoding="utf-8")
        missing = [needle for needle in needles if needle not in text]
        if missing:
            errors.append(
                f"{display_path(source, root)} missing {label}: "
                + ", ".join(f"`{needle}`" for needle in missing[:6])
                + ("" if len(missing) <= 6 else f", +{len(missing) - 6} more")
            )

    zipper_descend = root / "zipper-descend.egg"
    check_needles(
        zipper_descend,
        "full context datatype and relations",
        (
            "(datatype ZContext",
            "(RootCtx)",
            "(FrameCtx ZContext String Zipper)",
            "(TerminalFrameCtx ZContext String Zipper)",
            "(PatchFrameCtx ZContext String Zipper)",
            "(relation plugged (ZContext Zipper Zipper))",
            "(relation cursor (ZContext Zipper))",
            "(relation plug-source (ZContext Zipper))",
            "(relation down-move (ZContext Zipper String ZContext Zipper))",
            "(relation up-move (ZContext Zipper ZContext Zipper))",
            "(relation context-path (ZContext Path))",
            "(relation cursor-path (ZContext Zipper Path))",
            "(relation next-sibling-move (ZContext Zipper ZContext Zipper))",
            "(relation previous-sibling-move (ZContext Zipper ZContext Zipper))",
            "(relation next-sibling-target (ZContext Zipper ZContext Zipper))",
            "(relation previous-sibling-target (ZContext Zipper ZContext Zipper))",
        ),
    )
    check_needles(
        zipper_descend,
        "plug, move, path, and sibling rules",
        (
            "(plugged parent (UnionOp siblings (WrapOp focus (Item item))) whole)",
            "(plugged parent (UnionOp (TrieZ (Singleton (Eps))) (UnionOp siblings (WrapOp focus (Item item)))) whole)",
            "(plugged parent (PatchChildOp original item focus) whole)",
            "(down-move ctx focus item (PatchFrameCtx ctx item focus) (Child item focus))",
            "(up-move ctx focus parent (PatchChildOp original item focus))",
            "(plug-source parent (PatchChildOp original item focus))",
            "(cursor-path ctx focus path)",
            "(next-sibling-move ctx focus next-ctx next-focus)",
            "(previous-sibling-move ctx focus previous-ctx previous-focus)",
            "(adjacent-before item sibling)",
            "(adjacent-before sibling item)",
            "(has-key (PatchChildOp original item focus) sibling)",
            "(PatchFrameCtx parent sibling (PatchChildOp original item focus))",
            "(Child sibling (PatchChildOp original item focus))",
        ),
    )
    check_needles(
        zipper_descend,
        "normative context witnesses and negative probes",
        (
            "(let $ctx_a_with_d (FrameCtx (RootCtx) \"a\" (TrieZ $sd)))",
            "(let $ctx_terminal_a (TerminalFrameCtx (RootCtx) \"a\" (EmptyZ)))",
            "(check (plugged $ctx_a_with_d (TrieZ $sb) $plug_ab_with_d_impl))",
            "(check (plugged $ctx_terminal_a (EmptyZ) $plug_terminal_without_child_impl))",
            "(check (down-move (RootCtx) $virtual_context_parent \"a\" $virtual_context_child_ctx_a $virtual_context_child_a))",
            "(check (up-move $virtual_context_child_ctx_a $virtual_context_child_a (RootCtx) $virtual_context_up_a))",
            "(check (cursor-path $virtual_context_child_ctx_a $virtual_context_child_a $pa))",
            "(fail (check (cursor-path $virtual_context_child_ctx_a $virtual_context_child_a $pb)))",
            "(check (next-sibling-move $sibling_ctx_a $sibling_child_a $sibling_next_ctx_b $sibling_next_focus_b))",
            "(check (previous-sibling-move $sibling_next_ctx_b $sibling_next_focus_b $sibling_previous_ctx_a $sibling_previous_focus_a))",
            "(fail (check (next-sibling-move $sibling_next_ctx_b $sibling_next_focus_b $sibling_ctx_a $sibling_child_a)))",
        ),
    )

    context_egg = root / "zipper-egg-tests" / "context-movement.egg"
    context_source = root / "src" / "test" / "scala" / "ZipperEggContextMovementProgram.scala"
    generated_needles = (
        "Focus/context movement witness",
        "(datatype ZContext",
        "(PatchFrameCtx ZContext String Zipper)",
        "(rewrite (PatchChildOp parent item (Child item parent)) parent)",
        "(check (down-move (RootCtx) $parent \"a\" $ctx_a $child_a))",
        "(check (down-move (RootCtx) $nested_parent \"a\" $nested_ctx_a $nested_child_a))",
        "(check (down-move $nested_ctx_a $nested_child_a \"b\" $nested_ctx_ab $nested_child_b))",
        "(check (up-move $nested_ctx_ab $nested_child_b $nested_ctx_a $nested_up_b))",
        "(check (plugged $nested_ctx_ab $nested_child_b $nested_parent))",
        "(check (context-path $nested_ctx_ab $path_ab))",
        "(check (cursor-path $nested_ctx_ab $nested_child_b $path_ab))",
        "(check (next-sibling-target $ctx_a $child_a $ctx_b $child_b))",
        "(check (previous-sibling-target $ctx_b $child_b $ctx_a $child_a))",
        "(check (next-sibling-move $ctx_a $child_a $ctx_b $child_b))",
        "(check (previous-sibling-move $ctx_b $child_b $ctx_a $child_a))",
        "(fail (check (cursor-path $ctx_a $child_a $pb)))",
        "(fail (check (next-sibling-target $ctx_b $child_b $ctx_a $child_a)))",
        "(fail (check (next-sibling-move $ctx_b $child_b $ctx_a $child_a)))",
    )
    check_needles(context_egg, "generated patch-frame context regression", generated_needles)
    check_needles(context_source, "Scala-generated patch-frame context regression", generated_needles)

    if errors:
        return Result(
            "context movement acceptance invariant",
            "focus-context+plug-path-sibling",
            "invalid",
            False,
            root / "zipper-descend.egg",
            "; ".join(errors),
        )
    return Result(
        "context movement acceptance invariant",
        "focus-context+plug-path-sibling",
        "ok",
        True,
        root / "zipper-descend.egg",
        "full context datatype/rules, generated patch-frame regression, sibling/path probes, and FOL plug/graft/path artifacts are present",
    )


def validate_executable_zipper_context_acceptance(root: Path) -> Result:
    sources = [
        root / "src" / "main" / "scala" / "TrieSpace.scala",
        root / "src" / "test" / "scala" / "ZipperDenotationOracleTest.scala",
        root / "src" / "test" / "scala" / "TrieSpaceTest.scala",
    ]
    missing_sources = [source for source in sources if not source.exists()]
    errors: list[str] = []
    if missing_sources:
        errors.append(
            "missing executable zipper context source(s): "
            + ", ".join(display_path(source, root) for source in missing_sources)
        )

    def check_needles(source: Path, label: str, needles: tuple[str, ...]) -> None:
        if not source.exists():
            return
        text = source.read_text(encoding="utf-8")
        missing = [needle for needle in needles if needle not in text]
        if missing:
            errors.append(
                f"{display_path(source, root)} missing {label}: "
                + ", ".join(f"`{needle}`" for needle in missing[:6])
                + ("" if len(missing) <= 6 else f", +{len(missing) - 6} more")
            )

    trie_space = root / "src" / "main" / "scala" / "TrieSpace.scala"
    check_needles(
        trie_space,
        "concrete zipper path/context/edit/sibling API",
        (
            "trait ZipperContext:",
            "def path: Vector[Int]",
            "def plug(focus: TrieSpace): TrieSpace",
            "case object Root extends ZipperContext:",
            "case class Frame(parent: ZipperContext,",
            "override def path: Vector[Int] = parent.path :+ item",
            "override def plug(focus: TrieSpace): TrieSpace =",
            "case class Zipper(focus: TrieSpace, context: ZipperContext = ZipperContext.Root):",
            "def path: Vector[Int] = context.path",
            "def pathValue: PathValue = TrieSpace.decode(path)",
            "def whole: TrieSpace = context.plug(focus)",
            "def down(item: Int): Option[Zipper] =",
            "def descendItems(items: Iterable[Int]): Option[Zipper] =",
            "def up: Option[Zipper] = context match",
            "def toRoot: Zipper =",
            "def graft(replacement: TrieSpace): Zipper =",
            "def removeFocus: Zipper =",
            "def insertItemsAtFocus(path: List[Int]): Zipper =",
            "def firstChild: Option[Zipper] =",
            "def nextSibling: Option[Zipper] =",
            "def previousSibling: Option[Zipper] =",
            "private def sibling(delta: Int): Option[Zipper] = context match",
            ".sortWith((a, b) => TrieSpace.interner.compareItemIds(a._1, b._1) < 0)",
        ),
    )

    oracle = root / "src" / "test" / "scala" / "ZipperDenotationOracleTest.scala"
    check_needles(
        oracle,
        "bounded concrete zipper context oracle",
        (
            "test(\"concrete trie zipper plug reconstructs the whole at every focus\")",
            "val spaces = allSpaces(maxLen = 3)",
            "allFoci(space).foreach { cursor =>",
            "assertEquals(cursor.whole, space",
            "assertEquals(space.subtreeItems(cursor.path.toList).getOrElse(TrieSpace.empty), cursor.focus)",
            "cursor.up.foreach { parent =>",
            "assertEquals(parent.down(cursor.path.last).map(_.focus), Some(cursor.focus))",
            "assertEquals(cursor.toRoot.focus, space",
        ),
    )
    check_needles(
        oracle,
        "bounded concrete zipper edit and sibling oracle",
        (
            "test(\"concrete trie zipper supports focus edits and ordered sibling movement\")",
            "val grafted = atA.graft(replacement).whole",
            "val removed = atA.removeFocus.whole",
            "val inserted = atA.insertItemsAtFocus(x :: Nil).whole",
            "val next = atB.nextSibling.getOrElse(fail(\"missing next sibling\"))",
            "assertEquals(next.previousSibling.map(_.path), Some(Vector(b)))",
            "val nextAfterRemovedA = removedA.nextSibling.getOrElse(fail(\"missing next sibling after removed a\"))",
            "assertEquals(nextAfterRemovedA.previousSibling, None)",
            "val previousAfterRemovedC = removedC.previousSibling.getOrElse(fail(\"missing previous sibling after removed c\"))",
        ),
    )
    check_needles(
        oracle,
        "virtual zipper context oracle over operation-shaped foci",
        (
            "test(\"virtual zipper context movement plugs every operation-shaped focus\")",
            "\"memo\" -> SpaceZipper.Memo(SpaceZipper.Union(zx, zy))",
            "\"joinAll\" -> SpaceZipper.JoinAll(Vector(zx, zy, SpaceZipper.wrap(zx, d :: Nil)))",
            "\"intersection\" -> SpaceZipper.Intersection(zx, zy)",
            "\"meetAll\" -> SpaceZipper.MeetAll(Vector(zx, zy, SpaceZipper.wrap(zy, d :: Nil)))",
            "\"subtraction\" -> SpaceZipper.Subtraction(zx, zy)",
            "\"restriction\" -> SpaceZipper.Restriction(zx, zp)",
            "\"concat\" -> SpaceZipper.Concat(SpaceZipper.NonEmpty(zx), SpaceZipper.NonEmpty(zy))",
            "\"suffixClosure\" -> SpaceZipper.SuffixClosure(zx)",
            "\"tailsClosure\" -> SpaceZipper.TailsClosure(zx)",
            "\"range\" -> SpaceZipper.Range(zx, 1, x.pathCount.min(4))",
            "\"patchChild\" -> SpaceZipper.PatchChild(SpaceZipper.Union(zx, zy), a, SpaceZipper.singleton(c :: Nil))",
            "assertEquals(cursor.whole.materialize, expected",
            "assertEquals(parent.down(cursor.path.last).map(_.focus.materialize), Some(cursor.focus.materialize)",
            "assertEquals(cursor.toRoot.whole.materialize, expected",
        ),
    )
    check_needles(
        oracle,
        "virtual zipper lazy edit and sibling oracle",
        (
            "test(\"virtual zipper context graft edits focus through lazy patch frames\")",
            "val cursor = SpaceZipper.Cursor(root).down(a).getOrElse(fail(\"missing a focus\"))",
            "val edited = cursor.graft(replacement).whole",
            "assertEquals(edited.materialize, expected)",
            "assert(edited.concrete.isEmpty, \"virtual graft should remain a lazy zipper patch\")",
            "assertEquals(cursor.nextSibling.map(_.previousSibling.map(_.path)), Some(Some(cursor.path)))",
            "val removed = cursor.removeFocus",
            "val next = removed.nextSibling.getOrElse(fail(\"missing virtual next sibling after removed focus\"))",
            "assertEquals(next.previousSibling, None)",
            "val previous = removedC.previousSibling.getOrElse(fail(\"missing virtual previous sibling after removed focus\"))",
        ),
    )

    trie_test = root / "src" / "test" / "scala" / "TrieSpaceTest.scala"
    check_needles(
        trie_test,
        "public concrete zipper smoke test",
        (
            "val atA = root.down(PathItem(\"a\")).get",
            "val editedA = atA.graft(replacement)",
            "assertEquals(editedA.pathValue, Syntax.parse(\"a\"))",
            "val atB = editedA.nextSibling.get",
            "assertEquals(atB.pathValue, Syntax.parse(\"b\"))",
            "val backToA = atB.previousSibling.get",
            "val removedA = atA.removeFocus",
            "val bAfterRemoval = removedA.nextSibling.get",
        ),
    )

    if errors:
        return Result(
            "executable zipper context invariant",
            "path-plug-edit-sibling-oracles",
            "invalid",
            False,
            root / "src" / "test" / "scala" / "ZipperDenotationOracleTest.scala",
            "; ".join(errors),
        )
    return Result(
        "executable zipper context invariant",
        "path-plug-edit-sibling-oracles",
        "ok",
        True,
        root / "src" / "test" / "scala" / "ZipperDenotationOracleTest.scala",
        "concrete and virtual zipper path/plug/up/toRoot/edit/sibling API and bounded oracle coverage are present",
    )


def validate_transform_replacement_acceptance(artifacts: list[Artifact], root: Path) -> Result:
    sources = [
        root / "src" / "main" / "scala" / "MORKL.scala",
        root / "src" / "test" / "scala" / "OpenProgramProofArtifacts.scala",
        root / "src" / "test" / "scala" / "MORKL.scala",
        root / "src" / "test" / "scala" / "TrieSpaceTest.scala",
        root / "proofs" / "open" / "proof_manifest.tsv",
        root / "proofs" / "open" / "OPEN_PROGRAM_REPORT.md",
    ]
    missing_sources = [source for source in sources if not source.exists()]
    errors: list[str] = []
    if missing_sources:
        errors.append(
            "missing transform replacement source(s): "
            + ", ".join(display_path(source, root) for source in missing_sources)
        )

    def check_needles(source: Path, label: str, needles: tuple[str, ...]) -> None:
        if not source.exists():
            return
        text = source.read_text(encoding="utf-8")
        missing = [needle for needle in needles if needle not in text]
        if missing:
            errors.append(
                f"{display_path(source, root)} missing {label}: "
                + ", ".join(f"`{needle}`" for needle in missing[:6])
                + ("" if len(missing) <= 6 else f", +{len(missing) - 6} more")
            )

    main_morkl = root / "src" / "main" / "scala" / "MORKL.scala"
    if main_morkl.exists():
        text = main_morkl.read_text(encoding="utf-8")
        forbidden = (
            "case Transform",
            "Space.Transform",
            "Path.Transform",
            "Transform(",
        )
        found = [needle for needle in forbidden if needle in text]
        if found:
            errors.append(
                f"{display_path(main_morkl, root)} must not reintroduce Transform constructors/usages: "
                + ", ".join(f"`{needle}`" for needle in found)
            )

    open_programs = root / "src" / "test" / "scala" / "OpenProgramProofArtifacts.scala"
    check_needles(
        open_programs,
        "pure transform replacement open-program definition",
        (
            "open(\"transform-pair-swap-open\", Vector(SpaceMention(\"x\")),",
            "Unification.T(S\"x\", \"$left.$right\", \"$right.$left\")",
            "alphabet = Vector(\"a\", \"b\")",
            "maxLen = 2",
            "Space.Transform remains removed",
            "MORKL Unification.T expansion",
        ),
    )

    open_manifest = root / "proofs" / "open" / "proof_manifest.tsv"
    required_open_artifacts = {
        "transform-pair-swap-open:space_optimized_open": root / "proofs" / "open" / "smt2" / "transform_pair_swap_open_space_optimized_open.smt2",
        "transform-pair-swap-open:raw_graph_roundtrip_open": root / "proofs" / "open" / "smt2" / "transform_pair_swap_open_raw_graph_roundtrip_open.smt2",
        "transform-pair-swap-open:optimized_graph_roundtrip_open": root / "proofs" / "open" / "smt2" / "transform_pair_swap_open_optimized_graph_roundtrip_open.smt2",
    }
    if open_manifest.exists():
        rows = read_manifest(open_manifest, root)
        by_name = {artifact.name: artifact for artifact in rows}
        for name, expected_path in sorted(required_open_artifacts.items()):
            artifact = by_name.get(name)
            if artifact is None:
                errors.append(f"missing open manifest artifact `{name}`")
                continue
            if artifact.kind != "z3" or artifact.expected != "unsat":
                errors.append(f"{name} must be z3/unsat, got {artifact.kind}/{artifact.expected}")
            if artifact.artifact != expected_path:
                errors.append(
                    f"{name} points to {display_path(artifact.artifact, root)}, expected {display_path(expected_path, root)}"
                )
            if not artifact.artifact.exists():
                errors.append(f"{name} artifact missing at {display_path(artifact.artifact, root)}")

    open_report = root / "proofs" / "open" / "OPEN_PROGRAM_REPORT.md"
    check_needles(
        open_report,
        "transform replacement open-program report rows",
        (
            "| `transform-pair-swap-open` | `space_optimized_open` | `a,b` | `2` | `7` |",
            "| `transform-pair-swap-open` | `raw_graph_roundtrip_open` | `a,b` | `2` | `7` |",
            "| `transform-pair-swap-open` | `optimized_graph_roundtrip_open` | `a,b` | `2` | `7` |",
        ),
    )

    morkl_tests = root / "src" / "test" / "scala" / "MORKL.scala"
    check_needles(
        morkl_tests,
        "SpaceValue graph backend pure pair-swap regression",
        (
            "test(\"operation graph backend executes nested iteration rewrite and closure nodes\")",
            "val swapPairs = R\"swap_pairs\"(S\"pairs\") :=",
            "S\"pairs\".iter((P\"x\", P\"y\"), S\"_\", ss\"pair\" x sP\"y\" x sP\"x\")",
            "assert(swapCompiled.report.backendCompiled)",
            "assert(swapCompiled.report.backendUnsupported.isEmpty)",
            "exec(swapCompiled.graph.get, swapStack)",
            "assertEquals(swapStack.top.last.asInstanceOf[SpaceValue], SpaceValue(\"pair.b.a\", \"pair.d.c\"))",
        ),
    )

    trie_tests = root / "src" / "test" / "scala" / "TrieSpaceTest.scala"
    check_needles(
        trie_tests,
        "Trie graph backend pure pair-swap regression",
        (
            "test(\"operation graph trie backend covers pure pair swap and closure nodes\")",
            "val swapPairs = R\"swap_pairs\"(S\"pairs\") :=",
            "S\"pairs\".iter((P\"x\", P\"y\"), S\"_\", ss\"pair\" x sP\"y\" x sP\"x\")",
            "execTrie(tg, ts)",
            "assertEquals(ts.top.last.asInstanceOf[TrieSpace].toSpaceValue, SpaceValue(\"pair.b.a\", \"pair.d.c\"))",
        ),
    )

    if errors:
        return Result(
            "transform replacement invariant",
            "Space.Transform-absent+pure-Unification.T",
            "invalid",
            False,
            root / "src" / "test" / "scala" / "OpenProgramProofArtifacts.scala",
            "; ".join(errors),
        )
    return Result(
        "transform replacement invariant",
        "Space.Transform-absent+pure-Unification.T",
        "ok",
        True,
        root / "src" / "test" / "scala" / "OpenProgramProofArtifacts.scala",
        "Space.Transform remains absent and the pure Unification.T pair-swap replacement has open-program and backend regression coverage",
    )


def validate_termination_artifacts(root: Path) -> Result:
    sources = {
        "least_fixpoint_unique.p": (
            "least_fixpoint_unique",
            "l1_least",
            "l2_least",
            "cup_idempotent",
        ),
        "bounded_growth_decrease.p": (
            "bounded_growth_decrease",
            "subset(R,S)",
            "setminus(U,S)",
            "card_strict_decrease",
        ),
        "no_infinite_descent.smt2": (
            "no total function g from naturals to",
            "By steps 1+2, mathematical induction gives",
            "(check-sat) ; expect unsat",
        ),
        "transitive_equiv.p": (
            "transitive",
            "conjecture",
        ),
        "transitive_equiv.smt2": (
            "check-sat",
            "path2",
            "minimality",
        ),
        "datalog_a_terminates.p": (
            "bounded_growth_decrease",
            "terminates",
        ),
        "datalog_b_naive_terminates.p": (
            "bounded_growth_decrease",
            "terminates",
        ),
        "datalog_b_seminaive_terminates.p": (
            "bounded_growth_decrease",
            "terminates",
        ),
    }
    base = root / "terminating"
    errors: list[str] = []
    for name, needles in sources.items():
        path = base / name
        if not path.exists():
            errors.append(f"missing termination artifact {display_path(path, root)}")
            continue
        text = path.read_text(encoding="utf-8")
        missing = [needle for needle in needles if needle not in text]
        if missing:
            errors.append(
                f"{display_path(path, root)} missing termination proof markers: "
                + ", ".join(f"`{needle}`" for needle in missing)
            )
    if errors:
        return Result(
            "termination proof artifact invariant",
            "solver-runnable least-fixpoint+finite-growth+descent",
            "invalid",
            False,
            base,
            "; ".join(errors),
        )
    return Result(
        "termination proof artifact invariant",
        "solver-runnable least-fixpoint+finite-growth+descent",
        "ok",
        True,
        base,
        "terminating/ contains marker-checked, solver-runnable least-fixpoint uniqueness, finite-growth decrease, no-infinite-descent induction, transitive equivalence, and datalog termination obligations",
    )


def validate_range_acceptance(artifacts: list[Artifact], root: Path) -> Result:
    sources = [
        root / "zipper-descend.egg",
        root / "zipper-egg-tests" / "range-observation.egg",
        root / "zipper-egg-tests" / "range-border-child.egg",
        root / "zipper-egg-tests" / "range-border-operational.egg",
        root / "src" / "test" / "scala" / "ZipperEggTranspiler.scala",
    ]
    missing_sources = [source for source in sources if not source.exists()]
    errors: list[str] = []
    if missing_sources:
        errors.append(
            "missing Range source(s): "
            + ", ".join(display_path(source, root) for source in missing_sources)
        )

    by_name = {artifact.name: artifact for artifact in artifacts}
    required_artifacts = {
        "set_range_full_sentinel",
        "set_range_empty_one_one",
        "eager_range_set_equiv",
        "set_range_subset_fo",
        "set_range_first_terminal_fo",
        "zipper_range_materialization_equiv",
        "zipper_range_first_materialization_equiv",
        "zipper_range_last_materialization_equiv",
        "zipper_range_drop_last_materialization_equiv",
        "zipper_range_full_terminal_equiv",
        "zipper_range_first_terminal_fo",
        "set_range_first_child_terminal_empty_fo",
        "set_range_first_child_selected_sound_fo",
        "set_range_first_child_pruned_fo",
        "set_range_last_child_selected_sound_fo",
        "set_range_last_child_pruned_fo",
        "set_range_drop_last_child_before_last_fo",
        "set_range_drop_last_child_after_last_fo",
    }
    for name in sorted(required_artifacts):
        artifact = by_name.get(name)
        if artifact is None:
            errors.append(f"missing manifest artifact `{name}`")
            continue
        if artifact.kind != "vampire" or artifact.expected != "Theorem":
            errors.append(f"{name} must be vampire/Theorem, got {artifact.kind}/{artifact.expected}")
        if not artifact.artifact.exists():
            errors.append(f"{name} artifact missing at {display_path(artifact.artifact, root)}")

    def check_needles(source: Path, label: str, needles: tuple[str, ...]) -> None:
        if not source.exists():
            return
        text = source.read_text(encoding="utf-8")
        missing = [needle for needle in needles if needle not in text]
        if missing:
            errors.append(
                f"{display_path(source, root)} missing {label}: "
                + ", ".join(f"`{needle}`" for needle in missing[:6])
                + ("" if len(missing) <= 6 else f", +{len(missing) - 6} more")
            )

    zipper_descend = root / "zipper-descend.egg"
    check_needles(
        zipper_descend,
        "Range datatype, sentinels, and border relations",
        (
            "(RangeOp Zipper String String)",
            "(RangeFirstOp Zipper)",
            "(RangeLastOp Zipper)",
            "(RangeDropLastOp Zipper)",
            "(relation ordered-before (String String))",
            "(relation needs-first-head (Zipper))",
            "(relation needs-last-head (Zipper))",
            "(relation first-head (Zipper String))",
            "(relation last-head (Zipper String))",
            "(relation range-first-child-query (Zipper Zipper String))",
            "(relation range-last-child-query (Zipper Zipper String))",
            "(relation range-drop-last-child-query (Zipper Zipper String))",
            "(relation range-child-result (Zipper Zipper))",
            "(rewrite (RangeOp z \"0\" \"0\") z)",
            "(rewrite (RangeOp z \"1\" \"1\") (EmptyZ))",
            "(rewrite (RangeOp z \"0\" \"1\") (RangeFirstOp z))",
            "(rewrite (RangeOp z \"-1\" \"0\") (RangeLastOp z))",
            "(rewrite (RangeOp z \"0\" \"-1\") (RangeDropLastOp z))",
            "(rewrite (RangeOp z \"-2\" \"-1\") (RangeLastOp (RangeDropLastOp z)))",
        ),
    )
    check_needles(
        zipper_descend,
        "scheduled Range child and tail-frontier movement",
        (
            "(rule ((range-first-child-query z src item) (terminal src))",
            "((range-child-result z (EmptyZ)))",
            "(rule ((range-first-child-query z src item) (first-head src item))",
            "((range-child-result z (RangeFirstOp (Child item src))))",
            "(rule ((range-last-child-query z src item) (last-head src item))",
            "((range-child-result z (RangeLastOp (Child item src))))",
            "(rule ((range-drop-last-child-query z src item) (last-head src item))",
            "((range-child-result z (RangeDropLastOp (Child item src))))",
            "(rule ((range-drop-last-child-query z src item) (last-head src last) (ordered-before item last))",
            "((range-child-result z (Child item src)))",
            "(rule ((range-drop-last-child-query z src item) (last-head src last) (ordered-before last item))",
            "(rule ((range-first-child-query z src item) (range-child-result z result))",
            "((tail-frontier (RangeFirstOp src) item result))",
            "(rule ((range-last-child-query z src item) (range-child-result z result))",
            "((tail-frontier (RangeLastOp src) item result))",
            "(rule ((range-drop-last-child-query z src item) (range-child-result z result))",
            "((tail-frontier (RangeDropLastOp src) item result))",
        ),
    )
    check_needles(
        zipper_descend,
        "normative Range border witnesses and negative probes",
        (
            "(range-first-child-query $range_border_first_a $range_virtual_abc \"a\")",
            "(range-first-child-query $range_border_first_b $range_virtual_abc \"b\")",
            "(range-last-child-query $range_border_last_c $range_virtual_abc \"c\")",
            "(range-drop-last-child-query $range_border_drop_c $range_virtual_abc \"c\")",
            "(check (range-child-result $range_border_first_a (TrieZ $sb)))",
            "(check (range-child-result $range_border_first_b (EmptyZ)))",
            "(check (range-child-result $range_border_last_c (TrieZ $sd)))",
            "(check (range-child-result $range_border_drop_b (TrieZ $sc)))",
            "(check (range-child-result $range_border_drop_c (EmptyZ)))",
            "(check (tail-frontier (RangeFirstOp $range_virtual_abc) \"a\" (TrieZ $sb)))",
            "(check (tail-frontier (RangeLastOp $range_virtual_abc) \"b\" (EmptyZ)))",
            "(check (tail-frontier (RangeDropLastOp $range_virtual_abc) \"c\" (EmptyZ)))",
            "(check (empty-focus $miss_range_virtual_abc_first_prunes_middle_head))",
            "(check (empty-focus $miss_range_virtual_abc_drop_last_prunes_last_head))",
        ),
    )

    generic_range_rewrites: list[tuple[Path, int, str]] = []
    generic_needles = (
        "(Child item (RangeFirstOp src))",
        "(Child item (RangeLastOp src))",
        "(Child item (RangeDropLastOp src))",
    )
    for source in sources[:4]:
        if not source.exists():
            continue
        for kind, line, text in collect_egg_rules(source):
            if kind == "rewrite" and any(needle in text for needle in generic_needles):
                generic_range_rewrites.append((source, line, " ".join(part.strip() for part in text.splitlines() if part.strip())))
    if generic_range_rewrites:
        examples = "; ".join(
            f"{display_path(source, root)}:{line}:{text}"
            for source, line, text in generic_range_rewrites[:5]
        )
        suffix = "" if len(generic_range_rewrites) <= 5 else f"; +{len(generic_range_rewrites) - 5} more"
        errors.append(
            "Range child movement must stay scheduled through range-child-result/tail-frontier, "
            f"not generic eager Child(Range*) rewrites: {examples}{suffix}"
        )

    generated_files = {
        root / "zipper-egg-tests" / "range-border-child.egg": (
            "(let $first_unsorted_nested (RangeZ $unsorted_nested_src \"0\" \"1\"))",
            "(let $drop_last_four (RangeZ $four_src \"0\" \"-1\"))",
            "(check (range-child-result $unsorted_first_c (EmptyZ)))",
            "(check (range-child-result $four_drop_c $c_tail))",
            "(check (absent-key $drop_last_four \"e\"))",
            "(fail (check (range-child-result $four_drop_d $d_tail)))",
            "(fail (check (absent-key $drop_last_four \"c\")))",
        ),
        root / "zipper-egg-tests" / "range-observation.egg": (
            "(run-schedule (saturate range_border))",
            "(check (range-child-result $range_first_no_epsilon_a (RangeFirstOp (Child \"a\" $src_no_epsilon))))",
            "(check (range-child-result $range_last_b (RangeLastOp (Child \"b\" $src))))",
            "(check (range-child-result $range_drop_b (RangeDropLastOp (Child \"b\" $src))))",
            "(check (tail-frontier (RangeDropLastOp $src) \"c\" (EmptyZ)))",
        ),
        root / "zipper-egg-tests" / "range-border-operational.egg": (
            "(run-schedule",
            "(saturate normalize)",
            "(saturate observe)",
            "(saturate range_border)",
            "(check (range-child-result $concrete_first_a (TrieZ $sb)))",
            "(check (range-child-result $virtual_multi_first_a (RangeFirstOp (Child \"a\" $virtual_multi_ab))))",
            "(check (range-child-result $prefixed_drop_a (RangeDropLastOp (Child \"a\" $prefixed_src))))",
            "(fail (check (range-child-result $virtual_multi_first_a (Child \"a\" $virtual_multi_ab))))",
            "(fail (check (range-child-result $four_drop_d $d_tail)))",
        ),
    }
    for source, needles in generated_files.items():
        check_needles(source, "generated Range border regression", needles)

    transpiler = root / "src" / "test" / "scala" / "ZipperEggTranspiler.scala"
    check_needles(
        transpiler,
        "Scala generator hooks for Range artifacts",
        (
            "private val RangeObservationName = \"range-observation\"",
            "private val RangeBorderChildName = \"range-border-child\"",
            "private val RangeBorderOperationalName = \"range-border-operational\"",
            "val wantsRangeObservation = names.isEmpty || names(RangeObservationName)",
            "val wantsRangeBorderChild = names.isEmpty || names(RangeBorderChildName)",
            "val wantsRangeBorderOperational = names.isEmpty || names(RangeBorderOperationalName)",
            "writeRangeObservation(outDir)",
            "writeRangeBorderChild(outDir)",
            "writeRangeBorderOperational(outDir)",
            "\"range-observation.egg\"",
            "\"range-border-child.egg\"",
            "\"range-border-operational.egg\"",
        ),
    )

    if errors:
        return Result(
            "Range acceptance invariant",
            "ordered-border-state+generated-artifacts",
            "invalid",
            False,
            root / "zipper-descend.egg",
            "; ".join(errors),
        )
    return Result(
        "Range acceptance invariant",
        "ordered-border-state+generated-artifacts",
        "ok",
        True,
        root / "zipper-descend.egg",
        "Range sentinel semantics, ordered border-state child movement, generated artifacts, and unbounded FOL materialization/subset/child-border soundness artifacts are present",
    )


def validate_negative_key_acceptance(root: Path) -> Result:
    sources = [
        root / "zipper-descend.egg",
        root / "zipper-egg-tests" / "negative-key.egg",
        root / "src" / "test" / "scala" / "ZipperEggTranspiler.scala",
    ]
    missing_sources = [source for source in sources if not source.exists()]
    errors: list[str] = []
    if missing_sources:
        errors.append(
            "missing negative/key source(s): "
            + ", ".join(display_path(source, root) for source in missing_sources)
        )

    def check_needles(source: Path, label: str, needles: tuple[str, ...]) -> None:
        if not source.exists():
            return
        text = source.read_text(encoding="utf-8")
        missing = [needle for needle in needles if needle not in text]
        if missing:
            errors.append(
                f"{display_path(source, root)} missing {label}: "
                + ", ".join(f"`{needle}`" for needle in missing[:6])
                + ("" if len(missing) <= 6 else f", +{len(missing) - 6} more")
            )

    zipper_descend = root / "zipper-descend.egg"
    check_needles(
        zipper_descend,
        "key-set lattice and negative observation relations",
        (
            "(datatype KeySet",
            "(KEmpty)",
            "(KOne String)",
            "(KUnion KeySet KeySet)",
            "(KIntersection KeySet KeySet)",
            "(KDiff KeySet KeySet)",
            "(relation observed-key (String))",
            "(relation observable-focus (Zipper))",
            "(relation child-focus (Zipper String Zipper))",
            "(relation absent-key (Zipper String))",
            "(relation keyset (Zipper KeySet))",
            "(observed-key \"a\")",
            "(observed-key \"b\")",
            "(observed-key \"c\")",
            "(observed-key \"d\")",
            "(observed-key \"q\")",
            "(observed-key \"z\")",
            "(rule ((observed-key item) (observable-focus z))",
            "((child-focus z item (Child item z))))",
            "(rule ((child-focus z item child) (empty-focus child))",
            "((absent-key z item)))",
            "(rule ((has-key z item))",
            "((child-focus z item (Child item z))",
            "(observed-key item)))",
            "(rule ((has-key z item))",
            "((keyset z (KOne item))))",
        ),
    )
    check_needles(
        zipper_descend,
        "key-set non-collapse and precise has-key probes",
        (
            "(check (has-key $keys_union \"a\"))",
            "(check (has-key $keys_union \"b\"))",
            "(check (has-key $keys_intersection \"a\"))",
            "(fail (check (has-key $keys_intersection \"b\")))",
            "(check (has-key $keys_subtraction \"a\"))",
            "(fail (check (has-key $keys_subtraction \"b\")))",
            "(fail (check (has-key $exact_keys_subtraction_removed \"a\")))",
            "(fail (check (= (KEmpty) (KOne \"a\"))))",
            "(fail (check (= (KOne \"a\") (KOne \"b\"))))",
        ),
    )

    negative_key = root / "zipper-egg-tests" / "negative-key.egg"
    check_needles(
        negative_key,
        "generated negative-key regression",
        (
            "; Focused negative child-key observation witness.",
            "(relation observed-key (String))",
            "(relation absent-key (Zipper String))",
            "(rule ((observed-key item) (observable-focus z))",
            "((child-focus z item (Child item z))))",
            "(rule ((child-focus z item child) (empty-focus child))",
            "((absent-key z item)))",
            "(observed-key \"a\")",
            "(observed-key \"b\")",
            "(check (absent-key $diff_same \"a\"))",
            "(check (absent-key $intersection_disjoint \"a\"))",
            "(check (absent-key $restriction_prefix_miss \"a\"))",
            "(check (absent-key $concat_nonterminal_rhs \"b\"))",
            "(fail (check (absent-key $positive_union \"a\")))",
            "(fail (check (absent-key $positive_union \"b\")))",
        ),
    )

    transpiler = root / "src" / "test" / "scala" / "ZipperEggTranspiler.scala"
    check_needles(
        transpiler,
        "Scala generator hook for negative-key artifact",
        (
            "private val NegativeKeyName = \"negative-key\"",
            "val wantsNegativeKey = names.isEmpty || names(NegativeKeyName)",
            "writeNegativeKey(outDir)",
            "\"negative-key.egg\"",
        ),
    )

    if errors:
        return Result(
            "negative/key acceptance invariant",
            "relational-absence+keyset-noncollapse",
            "invalid",
            False,
            root / "zipper-descend.egg",
            "; ".join(errors),
        )
    return Result(
        "negative/key acceptance invariant",
        "relational-absence+keyset-noncollapse",
        "ok",
        True,
        root / "zipper-descend.egg",
        "negative key observation, keyset non-collapse probes, and generated negative-key regression are present",
    )


def operational_manifest_summary(path: Path) -> list[str]:
    rows = read_operational_manifest(path)
    if not rows:
        return [
            "",
            "## Operational Rule Manifest",
            "",
            f"- No operational manifest was found at `{path}`.",
        ]

    def inc(counter: dict[tuple[str, str], int], key: tuple[str, str]) -> None:
        counter[key] = counter.get(key, 0) + 1

    by_status_tier: dict[tuple[str, str], int] = {}
    op_counts: dict[str, int] = {}
    family_rows: dict[str, list[OperationalRule]] = {
        "Iter/Fixpoint/Head": [],
        "Range/Order": [],
        "Closure/Frontier": [],
        "Context/Patch": [],
    }
    family_ops = {
        "Iter/Fixpoint/Head": {
            "IterOp",
            "IterRangeTailOp",
            "IterRangeReconstructOp",
            "IterPrefixedRangeReconstructOp",
            "FixpointOp",
            "HeadOp",
            "iter-child-query",
            "iter-child-result",
            "fixpoint-child-query",
            "fixpoint-child-result",
            "fixpoint-unfold-query",
            "fixpoint-unfold-result",
        },
        "Range/Order": {
            "RangeOp",
            "RangeFirstOp",
            "RangeLastOp",
            "RangeDropLastOp",
            "needs-first-head",
            "needs-last-head",
            "first-head",
            "last-head",
            "range-first-child-query",
            "range-last-child-query",
            "range-drop-last-child-query",
            "range-child-result",
            "ordered-before",
        },
        "Closure/Frontier": {
            "TailsUnionOp",
            "TailsIntersectionOp",
            "PrefixClosureOp",
            "PrefixClosureBelowOp",
            "SuffixClosureOp",
            "TailsClosureOp",
            "FrontierUnionOp",
            "FrontierTailUnionOp",
            "FrontierChildUnionOp",
            "FrontierStateOp",
            "tail-frontier",
            "frontier-candidate",
            "frontier-union1-query",
            "frontier-union2-query",
            "frontier-union-result",
            "single-frontier",
        },
        "Context/Patch": {"plugged", "cursor", "down-move", "up-move", "next-sibling-move", "previous-sibling-move", "next-sibling-target", "previous-sibling-target", "context-path", "cursor-path", "PatchChildOp"},
    }
    for row in rows:
        inc(by_status_tier, (row.status, row.tier))
        for op in row.operations:
            op_counts[op] = op_counts.get(op, 0) + 1
        for family, ops in family_ops.items():
            if any(op in ops for op in row.operations):
                family_rows[family].append(row)

    stats = operational_manifest_stats(rows)
    pure_bounded = [row for row in rows if row.status == "proved-bounded" and row.tier == "bounded"]
    mixed = [row for row in rows if row.status == "proved-bounded" and row.tier == "mixed"]
    if stats.axiom_elsewhere == 0:
        axiom_note = "No `axiom-elsewhere` operational rows remain in the current manifest."
    else:
        axiom_note = "`axiom-elsewhere` rows are relational/scheduler helpers that need derivation from the unified semantic table."

    lines = [
        "",
        "## Operational Rule Manifest",
        "",
        f"- `{path}` contains `{stats.total}` operational rows: `{stats.proved_unbounded}` proved-unbounded, `{stats.proved_bounded}` proved-bounded, `{stats.axiom_elsewhere}` axiom-elsewhere, `{stats.unproved}` UNPROVED.",
        f"- Proof debt total: `{stats.proof_debt}` rows. `proved-bounded` rows are accepted by this gate but remain proof-strengthening work. {axiom_note} Of the proved-bounded rows, `{len(mixed)}` are mixed FOL+bounded and `{len(pure_bounded)}` are bounded-only.",
        "",
        "| Status | Tier | Rows |",
        "| --- | --- | --- |",
    ]
    for (status, tier), count in sorted(by_status_tier.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        lines.append(f"| `{status}` | `{tier}` | `{count}` |")

    lines.extend([
        "",
        "| Family | Rows | Proved-Unbounded | Proved-Bounded | Axiom-Elsewhere | UNPROVED |",
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ])
    for family, family_subset in family_rows.items():
        lines.append(
            f"| {family} | {len(family_subset)} | "
            f"{sum(1 for row in family_subset if row.status == 'proved-unbounded')} | "
            f"{sum(1 for row in family_subset if row.status == 'proved-bounded')} | "
            f"{sum(1 for row in family_subset if row.status == 'axiom-elsewhere')} | "
            f"{sum(1 for row in family_subset if row.status == 'UNPROVED')} |"
        )

    top_ops = sorted(op_counts.items(), key=lambda kv: (-kv[1], kv[0]))[:12]
    lines.extend([
        "",
        "- Highest-frequency operational symbols in the proof queue: "
        + ", ".join(f"`{op}` {count}" for op, count in top_ops)
        + ".",
    ])
    if pure_bounded:
        lines.extend([
            "",
            "Bounded-only rows to promote next:",
            "",
            "| Rule | Line | Operations | Note |",
            "| --- | ---: | --- | --- |",
        ])
        for row in pure_bounded[:20]:
            operations = ", ".join(f"`{op}`" for op in row.operations) or "_none_"
            lines.append(f"| `{row.rule_id}` | {row.line} | {operations} | {row.note} |")
    return lines


def run_parallel(artifacts: list[Artifact],
                 workers: int,
                 run_one) -> list[Result]:
    if not artifacts:
        return []
    results: list[Result | None] = [None] * len(artifacts)
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, workers)) as executor:
        futures = {
            executor.submit(run_one, artifact): i
            for i, artifact in enumerate(artifacts)
        }
        for future in concurrent.futures.as_completed(futures):
            results[futures[future]] = future.result()
    return [r for r in results if r is not None]


def markdown_report(
    args: argparse.Namespace,
    generation_results: list[Result],
    vampire_results: list[Result],
    z3_results: list[Result],
    egg_results: list[Result],
    vampire: str | None,
    root: Path,
) -> str:
    ok = all(r.ok for r in generation_results + vampire_results + z3_results + egg_results)
    manifest_stats = operational_manifest_stats(read_operational_manifest(root / args.operational_manifest))
    skipped_gates = []
    if args.no_vampire or not vampire:
        skipped_gates.append("Vampire")
    if args.no_z3:
        skipped_gates.append("Z3")
    if args.no_egg:
        skipped_gates.append("Egglog")
    if not ok:
        status = "FAIL"
    elif skipped_gates:
        status = "MANIFEST-ONLY" if len(skipped_gates) == 3 else "PARTIAL PASS"
    elif manifest_stats.proof_debt:
        status = "PASS_WITH_PROOF_DEBT"
    else:
        status = "PASS"
    alphabet = tuple(part for part in args.alphabet.split(",") if part)
    width = path_count(alphabet, args.max_len)
    lines = [
        "# Proof Pipeline Report",
        "",
        f"Status: {status}",
        "",
        "## Scope",
        "",
        "- Scala is the source of truth for generated proof and example egg artifacts.",
        "- `morkl.ProofArtifactGeneratorMain` generates SMT2 and TPTP files plus `proofs/proof_manifest.tsv`.",
        "- `morkl.generateZipperEggTests` generates the shared-prelude `formal.egg` and `zipper.egg` introductions plus the independent `zipper-egg-tests/*.egg` examples.",
        "- `morkl.generateCornerstoneProofArtifacts` generates exact-output SMT2/TPTP/egg certificates for aunt, semi-naive datalog, GOL, 15-puzzle, temperature, and n-queens.",
        "- `morkl.generateOpenProgramProofArtifacts` generates open-program SMT2 equivalence obligations over symbolic bounded input spaces plus structural full-program TPTP obligations.",
        f"- The runner emits `{args.operational_manifest}` by scanning every operational `(rewrite ...)` and `(rule ...)` in `zipper-descend.egg`, mapping semantic rows to proof artifacts where known, mapping path normalizers, memo/cache wrappers, and scheduler-observability helpers to explicit FOL contracts where available, keeping any remaining relational frontier/key scheduling helpers as `axiom-elsewhere`, and marking missing semantic coverage as `UNPROVED`.",
        "- This Python script runs external solvers/checkers against the Scala-generated artifacts and curated termination artifacts.",
        f"- Operational proof debt in this report: `{manifest_stats.proved_bounded}` proved-bounded rows, `{manifest_stats.axiom_elsewhere}` axiom-elsewhere rows, and `{manifest_stats.unproved}` UNPROVED rows. A zero-UNPROVED report is not the same as a fully unbounded proof.",
        "- Vampire runs in portfolio mode and proves first-order equivalence obligations connecting zipper membership, eager trie membership, and path-set membership. Iteration is represented as a general head/rest binder with arbitrary template-expression DAGs; body-union distribution, guarded invariant motion, and wrap/product/intersection/diff/restriction hoists have unbounded FOL obligations in addition to bounded counterexample checks.",
        "- TailsIntersection has an arbitrary-cardinality closed-frontier refinement theorem. The generated `tails-intersection-frontier.egg` artifact executes the corresponding demand-built key-list fold over a nested virtual union with a repeated head, demonstrating that same-head children merge before the all-head meet.",
        "- Core unit path-set algebra now has unbounded FOL obligations for union/intersection idempotence and associativity, diff self/union-right, child intersection/diff, restriction/raffination partition/disjointness, path concat epsilon normalization, memo/cache identity, and ordered Range child-border soundness/pruning facts. Operational rows that still cite bounded fixture-specific laws remain `proved-bounded` by weakest-tier accounting.",
        f"- Bounded universe: alphabet `{','.join(alphabet)}`, max path length `{args.max_len}`, `{width}` paths.",
        "- Valid laws are checked by asking Z3 for a counterexample to equality; `unsat` means no bounded counterexample was found.  The bounded law table includes MORKL-style Iteration with head/rest bindings.",
        "- Product/concatenation derivative laws are guarded by the principle `no concatenation escapes the bounded universe`: `child_product_*` uses a generated `ProductClosed(X,Y)` assumption that forbids exactly those X/Y path pairs whose concatenation would fall outside the bounded universe. Both `a` and `b` child representatives are checked, and the unguarded mutation must be `sat`.",
        "- Cornerstone example certificates are exact closed-program output equivalence checks generated from Scala after Scala has checked the compared evaluators/executors agree.",
        "- Open-program SMT certificates compare expanded source, source optimization, raw graph round-trip, and optimized graph round-trip for all symbolic inputs in each generated bounded universe.",
        "- Structural full-program FOL certificates emit generated MORKL program DAGs for Aunt, semi-naive Datalog, GOL, temperature, 2x2 sliding puzzle, the complete 24-state 2x2 sliding-puzzle step, and 4-queens, then prove source, optimized-source, trie, zipper, and graph backends equivalent using constructor-specific implementation lemmas over arbitrary input-space interpretations. `Iter` is modeled with an explicit path/space binding environment; `Range` is modeled as source membership plus ordered rank/bounds selection.",
        "- `terminating/` carries hand-staged termination and least-fixpoint artifacts: Vampire-checkable least-fixpoint uniqueness and finite-growth decrease lemmas, Z3-checkable no-infinite-descent induction steps, egglog sketches, and Datalog/transitive termination/equivalence obligations. These artifacts are executed by the corresponding gate unless that gate is skipped.",
        "- Arbitrary-data backend obligations use symbolic input spaces/templates to prove source, trie, zipper, and graph constructors agree independently of the concrete example data.",
        "- Negative controls are intentionally false laws; they must return `sat`.",
        f"- Vampire: {'available at `' + vampire + '`' if vampire else 'not installed; first-order proof phase skipped'}",
        f"- Per-obligation solver budgets: Z3 `{args.z3_time_limit}s`, Vampire `{args.vampire_time_limit}s`; solver obligations run with up to `{args.solver_workers}` workers.",
    ]
    if skipped_gates:
        lines.append(f"- Skipped gates in this run: {', '.join(skipped_gates)}.")
        lines.append("- Empty gate tables below mean the gate was skipped, not proved.")
    lines.extend([
        "",
        "## Scala Generation Gate",
        "",
        "| Step | Expected | Actual | Result |",
        "| --- | --- | --- | --- |",
    ])
    for r in generation_results:
        lines.append(f"| `{r.name}` | `{r.expected}` | `{r.actual}` | {'PASS' if r.ok else 'FAIL'} |")
    lines.extend([
        "",
        "## Vampire Equivalence Gate",
        "",
        "| Obligation | Expected | Actual | Result | Artifact |",
        "| --- | --- | --- | --- | --- |",
    ])
    for r in vampire_results:
        lines.append(f"| `{r.name}` | `{r.expected}` | `{r.actual}` | {'PASS' if r.ok else 'FAIL'} | `{r.artifact}` |")
    if not vampire_results:
        lines.append("| _skipped_ | `-` | `-` | SKIP | `-` |")
    lines.extend([
        "",
        "## Z3 Law Gate",
        "",
        "| Law | Expected | Actual | Result | Artifact |",
        "| --- | --- | --- | --- | --- |",
    ])
    for r in z3_results:
        lines.append(f"| `{r.name}` | `{r.expected}` | `{r.actual}` | {'PASS' if r.ok else 'FAIL'} | `{r.artifact}` |")
    if not z3_results:
        lines.append("| _skipped_ | `-` | `-` | SKIP | `-` |")
    lines.extend([
        "",
        "## Egglog Gate",
        "",
        "| Artifact | Expected | Actual | Result |",
        "| --- | --- | --- | --- |",
    ])
    for r in egg_results:
        lines.append(f"| `{r.name}` | `{r.expected}` | `{r.actual}` | {'PASS' if r.ok else 'FAIL'} |")
    if not egg_results:
        lines.append("| _skipped_ | `-` | `-` | SKIP |")
    lines.extend(operational_manifest_summary(root / args.operational_manifest))
    failures = [r for r in generation_results + vampire_results + z3_results + egg_results if not r.ok]
    if failures:
        lines.extend(["", "## Failures", ""])
        for r in failures:
            lines.extend([f"### {r.name}", "", "```", r.note[:4000], "```", ""])
    lines.extend([
        "",
        "## Limits",
        "",
        "- Vampire proves the abstraction and local constructor equivalence obligations listed above; it does not yet prove every optimizer rewrite directly from one generated semantic table.",
        "- The Z3 algebraic law phase is still a bounded finite-language check.",
        "- Iteration is now in the first-order and bounded proof layers, but arbitrary higher-order template equivalence is represented by schemas plus bounded examples rather than a generated semantic table.",
        "- Cornerstone example proofs are closed instantiated examples over their generated inputs/contexts; the open-program SMT tier covers proof-sized operator programs, benchmark skeletons, the full Aunt query over arbitrary bounded inputs, and a proof-sized full GOL helper expansion.",
        "- DAG-shared SMT emission is used for open-program obligations; whole programs with very large literal domains are better handled by the structural FOL tier.",
        "- The structural full-program FOL tier covers the six cornerstone examples plus a dedicated complete 24-state 2x2 sliding-puzzle step certificate. It uses constructor-specific backend equivalence lemmas and concrete literal/path definitions instead of one generic backend-denotation axiom. `Iter` now has an explicit environment-stack semantics for bound path refs and rest spaces, including nested iteration capture; `Range` now exposes membership, rank, count, normalized bounds, and half-open interval selection. `Fixpoint` now exposes the union-saturating base-or-step equation in the same structural environment, and `terminating/` adds staged least-fixpoint uniqueness plus finite-growth/descent termination evidence for representative recursion families. Full positivity/leastness obligations for arbitrary source `Fixpoint` and mutual recursion are still not discharged from one unified semantic table. `Fold` and grounded functions remain represented by shared operator semantic predicates; the next tightening step is to unfold those remaining predicates into stronger op-specific FOL lemmas.",
        "- Operational egg `Range` no longer has the four-path fixture-shaped answer rewrites for negative-window, `RangeLast`, or `RangeDropLast`. Negative-window now decomposes to `RangeLast(RangeDropLast(src))`; `RangeLast` and `RangeDropLast` over the concrete border fixture are handled by local terminal/child movement rules instead of whole-result materialization. Broad ordered-union rewrites and generic eager `Child(Range*)` rewrites crossed the OOM-safety threshold and are intentionally not used. The focused `range-border-child.egg` artifact validates the safer ordered border-state relation (`range-child-result`) with hit, miss, absent-key, and negative probes; `range-observation.egg` now covers both the concrete four-path epsilon/a.a/a.b/b.a border fixture and a no-epsilon first-border fixture through that scheduled relation; and `range-border-operational.egg` extends the relation to concrete trie unions, virtual unions, nested drop-last, and shared-prefix/prefixed Range sources under explicit normalize/observe/range-border phases. The proof layer now adds unbounded ordered-key FOL child-border obligations for first terminal/pruning, first/last selected soundness, last pruning, and drop-last before/after pruning. The remaining tightening step is to prove full selected-branch equality for drop-last and derive the egg scheduling relations directly from the unified semantic table instead of combining those FOL obligations with bounded generated witnesses.",
        "- The Antimirov closure-state operators now have bounded SMT artifacts for frontier union, keyed frontier tails, nested frontier child movement, and suffix/tails closure child states, plus named unbounded FOL child/nested-child bridge obligations for suffix/tails closure frontiers. Laws involving mutual recursion, leastness/positivity obligations for general Fixpoint lowering, and an unbounded bisimulation proof of the complete demand-driven frontier scheduler are not complete in this gate.",
        "- The main proof and runtime track is intentionally path-set-only. The value-payload experiment lives under `valued/` so the unit track can fully exploit stronger set laws and remain buildable with that directory removed.",
        "- `formal.egg` and `zipper.egg` share one Scala-generated core prelude and remain checked illustrative targets; `zipper-descend.egg` is the comprehensive operational target. Generated example egg files also come from Scala.",
        "",
    ])
    return "\n".join(lines)


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--alphabet", default="a,b", help="comma-separated finite alphabet")
    parser.add_argument("--max-len", type=int, default=3, help="maximum bounded path length")
    parser.add_argument("--out-dir", default="proofs/generated", help="where Scala writes generated SMT-LIB files")
    parser.add_argument("--vampire-out-dir", default="proofs/vampire/generated", help="where Scala writes generated TPTP files")
    parser.add_argument("--manifest", default="proofs/proof_manifest.tsv", help="Scala-generated artifact manifest")
    parser.add_argument("--example-out-dir", default="proofs/examples", help="where Scala writes cornerstone example proof artifacts")
    parser.add_argument("--example-manifest", default="proofs/examples/proof_manifest.tsv", help="Scala-generated cornerstone example manifest")
    parser.add_argument("--open-out-dir", default="proofs/open", help="where Scala writes open-program proof artifacts")
    parser.add_argument("--open-manifest", default="proofs/open/proof_manifest.tsv", help="Scala-generated open-program proof manifest")
    parser.add_argument("--operational-manifest", default="proofs/operational_rule_manifest.tsv", help="generated zipper-descend operational rule proof-coverage manifest")
    parser.add_argument("--report", default="proofs/PROOF_REPORT.md", help="markdown report path")
    parser.add_argument("--vampire", default="/Applications/Vampire", help="path to the Vampire executable")
    parser.add_argument("--vampire-time-limit", type=int, default=300, help="per-obligation Vampire time limit in seconds")
    parser.add_argument("--z3-time-limit", type=int, default=300, help="per-obligation Z3 time limit in seconds")
    parser.add_argument("--solver-workers", type=int, default=min(4, os.cpu_count() or 1), help="maximum parallel solver workers per solver family")
    parser.add_argument("--no-generate", action="store_true", help="do not regenerate SMT/TPTP artifacts from Scala")
    parser.add_argument("--no-example-generation", action="store_true", help="do not regenerate cornerstone example proof artifacts from Scala")
    parser.add_argument("--no-open-generation", action="store_true", help="do not regenerate open-program proof artifacts from Scala")
    parser.add_argument("--no-egg-generation", action="store_true", help="do not regenerate zipper-egg-tests/*.egg from Scala")
    parser.add_argument("--no-vampire", action="store_true", help="skip Vampire first-order proof obligations")
    parser.add_argument("--no-z3", action="store_true", help="skip Z3 bounded proof obligations")
    parser.add_argument("--no-egg", action="store_true", help="skip egglog artifact checks")
    parser.add_argument("--require-vampire", action="store_true", help="fail if vampire is unavailable")
    args = parser.parse_args(argv)

    root = Path(__file__).resolve().parents[1]
    generation_results: list[Result] = []

    if not args.no_generate:
        generation_results.append(run_scala_proof_generator(args, root))
        if not generation_results[-1].ok:
            report = markdown_report(args, generation_results, [], [], [], None, root)
            report_path = root / args.report
            report_path.parent.mkdir(parents=True, exist_ok=True)
            report_path.write_text(report, encoding="utf-8")
            print(f"FAIL scala proof artifact generation: {generation_results[-1].note}", file=sys.stderr)
            return 1

    if not args.no_example_generation:
        generation_results.append(run_scala_cornerstone_generator(args, root))
        if not generation_results[-1].ok:
            report = markdown_report(args, generation_results, [], [], [], None, root)
            report_path = root / args.report
            report_path.parent.mkdir(parents=True, exist_ok=True)
            report_path.write_text(report, encoding="utf-8")
            print(f"FAIL scala cornerstone proof generation: {generation_results[-1].note}", file=sys.stderr)
            return 1

    if not args.no_open_generation:
        generation_results.append(run_scala_open_program_generator(args, root))
        if not generation_results[-1].ok:
            report = markdown_report(args, generation_results, [], [], [], None, root)
            report_path = root / args.report
            report_path.parent.mkdir(parents=True, exist_ok=True)
            report_path.write_text(report, encoding="utf-8")
            print(f"FAIL scala open-program proof generation: {generation_results[-1].note}", file=sys.stderr)
            return 1

    manifest_path = root / args.manifest
    artifacts = read_manifest(manifest_path, root)
    example_manifest_path = root / args.example_manifest
    if example_manifest_path.exists():
        artifacts.extend(read_manifest(example_manifest_path, root))
    open_manifest_path = root / args.open_manifest
    if open_manifest_path.exists():
        artifacts.extend(read_manifest(open_manifest_path, root))
    product_guard_result = validate_product_mask_artifacts(artifacts, root)
    generation_results.append(product_guard_result)
    if not product_guard_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL product-guard artifact invariant: {product_guard_result.note}", file=sys.stderr)
        return 1
    negative_controls_result = validate_negative_control_families(artifacts, root)
    generation_results.append(negative_controls_result)
    if not negative_controls_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL negative-control family invariant: {negative_controls_result.note}", file=sys.stderr)
        return 1
    symbol_coverage_result = validate_symbol_coverage_artifacts(artifacts, root)
    generation_results.append(symbol_coverage_result)
    if not symbol_coverage_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL symbol-coverage invariant: {symbol_coverage_result.note}", file=sys.stderr)
        return 1
    negative_key_result = validate_negative_key_acceptance(root)
    generation_results.append(negative_key_result)
    if not negative_key_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL negative/key acceptance invariant: {negative_key_result.note}", file=sys.stderr)
        return 1
    closure_rewrite_result = validate_no_concrete_closure_rewrites(root)
    generation_results.append(closure_rewrite_result)
    if not closure_rewrite_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL concrete closure rewrite invariant: {closure_rewrite_result.note}", file=sys.stderr)
        return 1
    frontier_algebra_result = validate_frontier_algebra_rules(root)
    generation_results.append(frontier_algebra_result)
    if not frontier_algebra_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL frontier algebra rule invariant: {frontier_algebra_result.note}", file=sys.stderr)
        return 1
    iter_fixpoint_result = validate_iter_fixpoint_acceptance(artifacts, root)
    generation_results.append(iter_fixpoint_result)
    if not iter_fixpoint_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL iter/fixpoint acceptance invariant: {iter_fixpoint_result.note}", file=sys.stderr)
        return 1
    context_movement_result = validate_context_movement_acceptance(artifacts, root)
    generation_results.append(context_movement_result)
    if not context_movement_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL context movement acceptance invariant: {context_movement_result.note}", file=sys.stderr)
        return 1
    executable_context_result = validate_executable_zipper_context_acceptance(root)
    generation_results.append(executable_context_result)
    if not executable_context_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL executable zipper context invariant: {executable_context_result.note}", file=sys.stderr)
        return 1
    transform_replacement_result = validate_transform_replacement_acceptance(artifacts, root)
    generation_results.append(transform_replacement_result)
    if not transform_replacement_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL transform replacement invariant: {transform_replacement_result.note}", file=sys.stderr)
        return 1
    termination_result = validate_termination_artifacts(root)
    generation_results.append(termination_result)
    if not termination_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL termination proof artifact invariant: {termination_result.note}", file=sys.stderr)
        return 1
    range_acceptance_result = validate_range_acceptance(artifacts, root)
    generation_results.append(range_acceptance_result)
    if not range_acceptance_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL Range acceptance invariant: {range_acceptance_result.note}", file=sys.stderr)
        return 1
    op_manifest_result = generate_operational_rule_manifest(root, artifacts, root / args.operational_manifest)
    generation_results.append(op_manifest_result)
    if not op_manifest_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL operational rule manifest generation: {op_manifest_result.note}", file=sys.stderr)
        return 1
    op_manifest_closed_result = validate_operational_manifest_closed(root / args.operational_manifest)
    generation_results.append(op_manifest_closed_result)
    if not op_manifest_closed_result.ok:
        report = markdown_report(args, generation_results, [], [], [], None, root)
        report_path = root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report, encoding="utf-8")
        print(f"FAIL operational manifest closure invariant: {op_manifest_closed_result.note}", file=sys.stderr)
        return 1
    vampire_artifacts = [a for a in artifacts if a.kind == "vampire"]
    z3_artifacts = [a for a in artifacts if a.kind == "z3"]
    egg_artifacts = [a for a in artifacts if a.kind == "egg"]
    termination_vampire_artifacts, termination_z3_artifacts, termination_z3_multicheck_artifacts, termination_egg_artifacts = termination_solver_artifacts(root)
    vampire_artifacts.extend(termination_vampire_artifacts)
    z3_artifacts.extend(termination_z3_artifacts)

    z3 = None if args.no_z3 else shutil.which("z3")
    if not args.no_z3 and not z3:
        print("z3 not found on PATH", file=sys.stderr)
        return 2
    vampire_candidate = Path(args.vampire)
    vampire = str(vampire_candidate) if vampire_candidate.exists() else shutil.which("vampire")
    if not args.no_vampire and not vampire:
        print("vampire not found on PATH and --vampire does not exist", file=sys.stderr)
        return 2
    if args.require_vampire and not vampire:
        print("vampire not found on PATH", file=sys.stderr)
        return 2

    vampire_results: list[Result] = []
    if not args.no_vampire and vampire:
        vampire_results = run_parallel(
            vampire_artifacts,
            args.solver_workers,
            lambda artifact: run_vampire(vampire, artifact, root, args.vampire_time_limit),
        )

    z3_results: list[Result] = []
    if not args.no_z3:
        z3_work = z3_artifacts + termination_z3_multicheck_artifacts
        z3_results = run_parallel(
            z3_work,
            args.solver_workers,
            lambda artifact: run_z3_multicheck(z3, artifact, root, args.z3_time_limit)
            if artifact.kind == "z3-multicheck"
            else run_z3(z3, artifact, root, args.z3_time_limit),
        )

    egg_results: list[Result] = []
    if not args.no_egg:
        if not args.no_egg_generation:
            generation_results.append(run_scala_egg_generator(root))
        egglog = shutil.which("egglog")
        if not egglog:
            egg_results.append(Result("egglog", "available", "missing", False, "egglog", "egglog not found on PATH"))
        elif all(r.ok for r in generation_results):
            egg_results.append(run_process("formal.egg", [egglog, "formal.egg"], root))
            egg_results.append(run_process("zipper-descend.egg", [egglog, "zipper-descend.egg"], root))
            egg_results.append(run_process("zipper.egg", [egglog, "zipper.egg"], root))
            for artifact in termination_egg_artifacts:
                egg_results.append(run_process(str(artifact.relative_to(root)), [egglog, str(artifact)], root))
            for artifact in sorted((root / "zipper-egg-tests").glob("*.egg")):
                egg_results.append(run_process(str(artifact.relative_to(root)), [egglog, str(artifact)], root))
            for artifact in sorted(egg_artifacts, key=lambda a: str(a.artifact)):
                egg_results.append(run_process(str(display_path(artifact.artifact, root)), [egglog, str(artifact.artifact)], root))

    report = markdown_report(args, generation_results, vampire_results, z3_results, egg_results, vampire, root)
    report_path = root / args.report
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(report, encoding="utf-8")

    for result in generation_results + vampire_results + z3_results + egg_results:
        status = "PASS" if result.ok else "FAIL"
        print(f"{status:4} {result.name}: expected {result.expected}, got {result.actual}")

    return 0 if all(r.ok for r in generation_results + vampire_results + z3_results + egg_results) else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
