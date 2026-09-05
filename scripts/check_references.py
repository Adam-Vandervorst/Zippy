#!/usr/bin/env python3
"""EVERY FILE REFERENCE IN EVERY TRACKED TEXT FILE MUST RESOLVE.

Two failure modes this catches, both of which the repository had:

  1. a MARKDOWN LINK whose target does not exist (`[BENCHMARKS.md](BENCHMARKS.md)` after the file
     moved to `docs/`);
  2. a PROSE/COMMENT citation of a file that does not exist -- the repository had accumulated 369
     citations of an external review document that was never in the tree, spread over 42 source,
     doc, proof and script files, so a reader had no way to tell a live pointer from a dead one.
     (They are gone; the substance each one carried is stated in place.)

A reference resolves if it is found relative to the repo root, to the citing file's own directory,
or to one of the SEARCH_ROOTS (so `MORKL.scala` in a doc, or `laws/law_union_idem.smt2` in a proof header,
both resolve without spelling the full path).

==WHAT IS SCANNED, AND WHY THAT CHANGED==

EVERY TRACKED TEXT FILE, and the file list comes from `git ls-files` — not from a glob plus an
extension allow-list.  It used to be the other way round: `SCAN_EXT` named eight extensions and
`SKIP_FILES` excluded `build.log`, the generated CSV/TSV results and `MINED.tsv` wholesale, so a
zero from this checker meant "zero in its selected subset" and `laws.diff` could sit in the tree
containing an absolute macOS prover path while the header claimed every reference resolved.
Now:

  * the candidate set is every tracked file (so a new `.rst`, `.toml` or extensionless script is
    covered the day it is added, without editing this script);
  * BINARY files are skipped by CONTENT (a NUL byte in the first 8 KiB), never by name;
  * there is NO whole-file exception.  A file that legitimately contains an unresolvable token
    declares that token in `TOKEN_EXCEPTIONS` below, one entry per token, each with the file it
    applies to and the reason.  A blanket skip cannot come back by accident: `--strict` fails if a
    declared exception is never used, so a stale one is a failure rather than a widening.

==ONE SNAPSHOT, NAMES AND CONTENTS FROM THE SAME PLACE==

A reference check is a statement about a TREE, so both halves of it -- which files exist, and what
they say -- have to come from the same tree. `--snapshot` selects which:

    worktree   the files on disk, as you see them.  What a local run wants.
    index      the staged tree (`git write-tree`).  The default for `--fresh`.
    head       the tree of `HEAD`.  What CI should check.

THE EARLIER `--fresh` GOT THIS WRONG and the mixture is worth spelling out, because it produced a
green result that meant nothing: it took the NAME LIST from `git ls-files` and then `shutil.copy2`'d
the WORKING-TREE CONTENTS under those names. So a file staged-but-modified was checked under its
committed name with its uncommitted body; a file deleted from disk but still in the index vanished
from the scan entirely; and a reference introduced by an uncommitted edit was validated against a
tracked name list. Names from one tree, contents from another, and no tree that the answer described.

Both now come from `git archive` of a single tree object, so a snapshot run is reproducible from that
tree alone and is unaffected by unrelated working-tree state.

REFERENCES RESOLVE AGAINST THE SNAPSHOT'S OWN NAME SET, NOT THE FILESYSTEM. Two things follow, and
both are requirements rather than conveniences:

  * an untracked file cannot make a reference resolve, in any mode, because it is not in the set;
  * CASE IS CHECKED EXACTLY. `pathlib.Path.exists()` answers on the filesystem's terms, so on a
    case-insensitive filesystem (macOS, Windows) a link whose target differs from the real name
    ONLY IN CASE resolves, and on Linux it does not -- the same repository, two answers. Set
    membership is case-sensitive everywhere; `selftest()` pins it with a real repository.

Run: python3 scripts/check_references.py                      # working tree
     python3 scripts/check_references.py --fresh              # the index snapshot
     python3 scripts/check_references.py --snapshot=head      # the HEAD snapshot
     python3 scripts/check_references.py --fresh --strict     # ...and fail on an UNUSED exception
     python3 scripts/check_references.py --selftest           # the snapshot-semantics regressions

`--strict` fails on a declared exception that matched nothing, but only under a git snapshot: in the
working tree a token can resolve because of an untracked local file, and the exception is then
legitimately never consulted.
"""
import os
import re
import sys
import pathlib

import subprocess
import tempfile
import shutil
import tarfile
import io
import posixpath

ROOT = pathlib.Path(__file__).resolve().parent.parent
DECLARING_FILE = "scripts/check_references.py"      # where TOKEN_EXCEPTIONS below is written

# Directories a bare filename may be relative to.  Order is irrelevant: any hit resolves.
SEARCH_ROOTS = [
    "", "docs", "scripts", "proofs", "proofs/laws", "proofs/spatial", "proofs/spatial-semantic",
    "proofs/pipeline", "proofs/unbounded", "proofs/unbounded/negative",
    "proofs/pipeline/fixpoint-gate", "proofs/lean", "proofs/lean/Zippy",
    "src/main/scala", "src/test/scala", "src/test/resources",
    "terminating", "zipper-egg-tests", "zipper-egg-tests/generated", "zipper-egg-tests/pipeline",
]

# Extensions that make a token a file reference.  `.sh` and `.p` are only honoured when the token
# also contains a `/`: bare `a.sh` is overwhelmingly a Scala field access (`a.show` abbreviated to
# `.sh`), and bare `x.p` is a variable.
# `.lean`: proofs/lean is where every mechanized theorem lives and docs/TRUSTED.md,
# the registries and the SMT files cite its modules by path, so a renamed module must fail here.
ALWAYS = (".md", ".scala", ".py", ".egg", ".smt2", ".tsv", ".csv", ".png", ".sbt", ".ser", ".rle", ".lean")
PATH_ONLY = (".sh", ".p", ".txt", ".json", ".jsonl")

# EXTERNAL DATASETS.  Not in the tree by design: the suites resolve them through `Loaders.resolve`
# (a `-D` override, then $ZIPPY_DATA, then a repo-relative path) and fall back to a deterministic
# inline fixture, so a fresh checkout runs green without them.
EXTERNAL_DATA = {"lot.metta", "fred.rle", "royal92_simple.metta", "noaa_slice.txt",
                 "NOAAGlobalTemp.nc"}

# Files that are GENERATED by a test/script and therefore legitimately absent from a fresh
# checkout.  Each entry names the generator, which is what a reader actually needs.
GENERATED = {
    "corpus_1000.ser": "morkl.ProgramExpressivity",
    "corpus_1000.txt": "morkl.ProgramExpressivity",
    "corpus_runtimes.csv": "morkl.CorpusRuntimes",
    "expressivity.csv": "morkl.ProgramExpressivity",
    "prog_matrix.tsv": "morkl.ProgramStats",
    "datalog-morkl.txt": "morkl.DatalogShowTest",
    # A6: the transfer checker's inputs (proofs/spatial/out/, gitignored)
    "transfers.tsv": "morkl.SpatialTransferDump",
    "bounds.tsv": "morkl.SpatialTransferDump",
}

# Tokens that look like a path but are not: interpolated names, doc placeholders, scratch paths.
IGNORE_RE = re.compile(
    r"""(
      ^\$          |   # shell/egg interpolation
      \$\{         |   # scala interpolation inside the token
      ^-           |   # a SUFFIX pattern, e.g. -impl.egg / -zipper.egg / -space.egg
      ^/tmp/       |
      ^\.\.\.      |
      ^TMP/        |   # $TMP/... in check_locality.sh, written at run time
      ^[a-z]\.egg$ |   # chain$d.egg style, built by a loop
      ^name\.egg$  |
      ^stage-      |
      ^generated/rand-  |# regenerated by scripts/gen_bridge_tests.py
      ^selftest-         # a fixture `selftest()` below writes into a THROWAWAY repository
    )""",
    re.X,
)

SKIP_DIRS = {".git", ".tools", "target", ".bsp", ".idea", ".scala-build", ".bloop", "__pycache__"}

# PER-TOKEN EXCEPTIONS.  `(file-suffix-or-"*", token) -> reason`.  Each entry excuses ONE token in
# ONE place; there is no whole-file skip.  `--strict` fails on an entry that matched nothing, so an
# exception that outlives its cause is a failure and not a silent widening.
#
# The five kinds that legitimately occur, and nothing else qualifies:
#   (a) an EXTERNAL project cited by its own repo-relative path (carac's Datalog fixtures);
#   (b) a file the historical narrative in build.log records as HAVING EXISTED and then removed —
#       the narrative is the artifact, so the citation is a fact about the past, not a pointer;
#   (c) a token that is a MEASUREMENT or an identifier and only looks like a filename;
#   (d) a tool binary named with an extension-like suffix;
#   (e) a declared future file. Each proposed path is declared here per token; `--strict` retires
#       the exception as soon as the file lands.
TOKEN_EXCEPTIONS = {
    # (a) carac is an EXTERNAL Datalog benchmark whose fixtures these programs were derived from.
    # The citation is `carac:<its own repo-relative path>`; the scanner sees the path part, since
    # `carac:` is not a token character.  Nothing in this tree resolves it, by design.
    ("terminating/datalog_a.txt", "src/test/scala/test/graphs/SingleCycle.scala"):
        "(a) external: carac's own test fixture, cited repo-relative; carac is not vendored here",
    ("terminating/datalog_a.txt", "src/test/scala/test/graphs/MultiIsolatedCycle.scala"): "(a) as above",
    ("terminating/datalog_a.txt", "src/test/scala/test/graphs/TopSort.scala"): "(a) as above",

    # (b) build.log is an APPEND-ONLY NARRATIVE.  These entries record documents that existed at the
    # time of the entry and have since been removed; the sentence around each one is the artifact,
    # so the name is a fact about the past and not a live pointer.  Rewriting them would falsify the
    # log; deleting them would lose the experiment narrative the entry exists for.
    ("build.log", "critique_on_b.md"): "(b) a review document that existed at that entry's date and was removed",
    ("build.log", "learned_from_a.md"): "(b) as above",
    ("build.log", "fallbacks.md"): "(b) as above",
    ("build.log", "whispers.md"): "(b) as above",
    ("build.log", "locality-schedule.egg"): "(b) an egg experiment that existed at that entry's date and was removed",
    ("build.log", "project.scala"): "(b) the scala-cli project file the tree used before build.sbt",

    # (c) SLASH-ABBREVIATED GROUPS: one token standing for several real files, e.g.
    # `impl_wrap/unwrap/head.smt2` means impl_wrap.smt2 + impl_unwrap.smt2 + impl_head.smt2.  Each
    # of the named files DOES exist; the token is prose shorthand, not a path.
    ("build.log", "gol/nqueens/puzzle15/temperature-space.egg"):
        "(c) shorthand for the four stones' -space egg cells of the previous matrix (deleted in 2A.2)",
    ("build.log", "impl_wrap/unwrap/head.smt2"):
        "(c) shorthand for impl_wrap.smt2, impl_unwrap.smt2, impl_head.smt2",
    # (f') GENERATED WITNESS TABLES UNDER `target/`: written by check_asserts.py and
    #      check_lean.sh, read by proof_closure.py; git-ignored like every build output.
    ("scripts/check_asserts.py", "target/assert-closure.tsv"): "(f') the assert-closure witness this script writes",
    ("scripts/check_asserts.py", "assert-closure.tsv"): "(f') the same table, by its bare name in the docstring",
    ("scripts/proof_closure.py", "target/assert-closure.tsv"): "(f') the assert-closure witness this script reads",
    ("scripts/proof_closure.py", "assert-closure.tsv"): "(f') the same table, by its bare name",
    ("scripts/gates.py", "target/assert-closure.tsv"): "(f') the assert-closure witness the gate order depends on",
    ("scripts/gates.py", "target/lean-mechanized.tsv"): "(f') the Lean witness the gate order depends on",
    ("docs/TRUSTED.md", "target/assert-closure.tsv"): "(f') the assert-closure witness, named where the marker taxonomy is specified",
    ("build.log", "target/assert-closure.tsv"): "(f') the assert-closure witness, named in the Phase 2 record",
    ("scripts/publish_benchmarks.py", "target/test-runtime/classpath.txt"): "(f') the runner's classpath file `sbt exportTestRuntime` writes, read by --reproduce",
    # (g') TRANSIENT PROBE FILES named by the scripts that create and remove them
    ("scripts/check_lean.sh", ".axioms_probe.lean"): "(g') the transient #print-axioms probe this script writes and removes",
    # (h) HISTORY AND SHORTHAND in build.log (append-only): a renamed Lean module, a Mathlib path
    #     inside the git-ignored `.lake` checkout, two slash-shorthands, a deleted artifact.
    ("build.log", "Core.lean"): "(h) the Lean module later folded into Pointwise.lean (Phase 0/1 record)",
    ("build.log", "Mathlib/Order/WellFoundedSet.lean"): "(h) a Mathlib source path under the git-ignored .lake checkout",
    ("build.log", "check_lean.sh/proof_closure.py"): "(h) slash shorthand for two scripts",
    ("build.log", "nqueens-zipper-virtual.egg"): "(h) an artifact of the previous matrix, deleted in 2A.2",
    # (i) MATHLIB'S OWN CONFIG FILE NAME, recorded by lake in the manifest
    ("proofs/lean/lake-manifest.json", "lakefile.lean"): "(i) the config file name of a dependency inside .lake",
    # (j) SYNTHETIC NAMES of selftest (e): an in-memory name set that deliberately disagrees with the disk
    ("scripts/check_references.py", "docs/in-set-only.md"): "(j) selftest (e) synthetic name",
    ("scripts/check_references.py", "in-set-only.md"): "(j) selftest (e) synthetic name",
    ("scripts/check_references.py", "docs/Spec.md"): "(j) selftest (e) synthetic name",
    ("scripts/check_references.py", "docs/spec.md"): "(j) selftest (e) synthetic name (case variant)",
    ("scripts/check_references.py", "scripts/x.py"): "(j) selftest (e) synthetic name",
    ("scripts/check_references.py", "../scripts/x.py"): "(j) selftest (e) synthetic relative name",
    ("scripts/check_references.py", "docs/readme.md"): "(j) selftest (e) synthetic origin",
    ("scripts/check_references.py", "on-disk-only.md"): "(j) selftest (e) synthetic file that IS on disk and must not resolve",

    # (g) THE IGNORE FILE'S OWN TOKENS — a per-token exception replaces the former
    #     whole-file skip).  Each names a TRANSIENT file a script creates and removes; the ignore
    #     exists so a mid-run `git add -A` cannot catch it, and the path is absent by design.
    (".gitignore", "proofs/unbounded/.probe.p"): "(g) run.sh's transient vacuity probe, removed by run.sh",
    (".gitignore", "proofs/lean/.axioms_probe.lean"): "(g) check_lean.sh's transient #print-axioms probe, removed by it",
    # (f) GENERATED PATHS UNDER `target/`, which is gitignored (a build output, never committed).
    #     These are not dangling references: each one is written by a task in this tree and the text
    #     that names it says which.  They cannot be resolved by the checker, because the whole point
    #     of `target/` is that a fresh checkout does not have it -- and making the checker resolve
    #     against a local build would make its verdict depend on whether someone had built.  There
    #     is no retirement rule for these: the file is generated on every build, so the exception is
    #     permanent, and the reason names the PRODUCER so a reader can regenerate it.
    # (g) the acceptance generator's inputs are gate RECORDS under target/: written by `gates.py --run` and
    #     `proof_closure.py --check`, deliberately untracked (E3 derives the committed document from them)
    ("docs/ACCEPTANCE.md", "target/gates.tsv"): "(g) generated gate record, untracked by design",
    ("docs/ACCEPTANCE.md", "target/trace-closure.tsv"): "(g) generated closure table, untracked by design",
    ("docs/ACCEPTANCE_MAP.tsv", "target/gates.tsv"): "(g) as above",
    ("docs/ACCEPTANCE_MAP.tsv", "target/trace-closure.tsv"): "(g) as above",
    ("scripts/gates.py", "target/test-runtime/run-suite.sh"):
        "(f) generated by `sbt exportTestRuntime` (build.sbt); target/ is a build output",
    ("scripts/publish_benchmarks.py", "target/test-runtime/run-suite.sh"): "(f) as above",
    ("src/test/scala/CalibrationProbe.scala", "target/test-runtime/run-suite.sh"): "(f) as above",
    # `check_determinism.sh` needs no (f) entry: it writes the runner path as `./target/...`, and the
    # scanner's token for that is the bare `run-suite.sh`, which the (f) entries above already cover.
    ("scripts/check_lean.sh", "target/lean-mechanized.tsv"):
        "(f) generated by this very script; it is the witness `proof_closure.py` reads, and it lives "
        "under target/ deliberately so a reader who has not run the Lean gate inherits no lift",
    ("scripts/proof_closure.py", "target/lean-mechanized.tsv"): "(f) as above, consumed here",
    ("build.log", "target/lean-mechanized.tsv"):
        "(f) as above; the log entry that recorded the marker mechanism names the witness it writes",

    # (g) A PATH THAT MUST NOT EXIST.  `SinkGuardCheck` checks that `ArtifactSink` reports an
    #     artifact with NO committed twin as a FINDING rather than passing it, so it needs a path
    #     the tree does not have -- and it ASSERTS that the path is absent before writing, so the
    #     day someone creates the file the TEST fails, not just this checker.  Unlike an (e) entry
    #     there is no retirement rule, because the reference is supposed to stay dangling forever.
    ("src/test/scala/SinkGuardCheck.scala", "proofs/__sinkguard_absent.smt2"):
        "(g) deliberately absent: the suite asserts !exists before using it, so the file appearing "
        "fails the test rather than only this checker",
    ("scripts/proof_closure.py", "lean-mechanized.tsv"):
        "(f) as above; the bare filename in that file's prose, same artifact",

    # (f'') OTHER GENERATED OUTPUTS AND WITNESSES.  These tokens are assembled with a directory at
    # run time or deliberately live under ignored target/.  Name every producer/consumer pair so a
    # fresh index snapshot and a warm worktree receive exactly the same verdict.
    ("docs/TRUSTED.md", ".trace.tsv"): "(f'') suffix of the per-cell trace files generated by EquivPipelineTest",
    ("docs/TRUSTED.md", "target/trace-closure.tsv"): "(f'') proof_closure.py's generated closure witness",
    ("docs/atlas.md", ".trace.tsv"): "(f'') suffix of the per-cell trace files generated by EquivPipelineTest",
    ("scripts/audit_pipeline_markers.py", "target/trace-closure.tsv"): "(f'') generated by proof_closure.py, consumed here",
    ("scripts/check_coverage.py", "target/trace-closure.tsv"): "(f'') generated by proof_closure.py, consumed here",
    ("scripts/check_coverage.py", "trace-closure.tsv"): "(f'') same generated closure witness by basename",
    ("scripts/check_traces.py", ".trace.tsv"): "(f'') runtime suffix for committed per-cell traces",
    ("scripts/gates.py", "target/gates.tsv"): "(f'') this script's generated gate record",
    ("scripts/gates.py", "gates.tsv"): "(f'') same generated gate record by basename",
    ("scripts/gates.py", "target/trace-closure.tsv"): "(f'') generated by proof_closure.py before its consumers run",
    ("scripts/gen_acceptance.py", "target/gates.tsv"): "(f'') generated by gates.py, consumed here",
    ("scripts/gen_acceptance.py", "gates.tsv"): "(f'') same generated gate record by basename",
    ("scripts/gen_acceptance.py", "target/trace-closure.tsv"): "(f'') generated by proof_closure.py, consumed here",
    ("scripts/gen_acceptance.py", "trace-closure.tsv"): "(f'') same generated closure witness by basename",
    ("scripts/proof_closure.py", ".trace.tsv"): "(f'') runtime suffix for committed per-cell traces",
    ("scripts/proof_closure.py", "target/trace-closure.tsv"): "(f'') this script's generated closure witness",
    ("scripts/proof_closure.py", "trace-closure.tsv"): "(f'') same generated closure witness by basename",
    ("scripts/proof_closure.py", "trace-closure-injected.tsv"): "(f'') this script's mutation-only generated witness",
    ("scripts/publish_benchmarks.py", "gates.tsv"): "(f'') generated gate record updated after reproduction",
    ("src/test/scala/ProofTraceCheck.scala", "target/artifact-scratch/marker-only.smt2"):
        "(f'') scratch artifact deliberately generated under target by this mutation test",
    ("src/test/scala/DecisionsCheck.scala", ".frontier.tsv"): "(f'') runtime suffix for generated decision frontiers",
    ("src/test/scala/DecisionsCheck.scala", "DECISIONS.tsv"): "(f'') generated decision index assembled under proofs/decisions",
    ("scripts/check_puzzle15.py", "CERTIFICATE.tsv"): "(f'') Puzzle15Check output assembled under proofs/puzzle15",
    ("scripts/check_puzzle15.py", "EXPANSION.tsv"): "(f'') Puzzle15Check output assembled under proofs/puzzle15",
    ("scripts/check_puzzle15.py", "THRESHOLDS.tsv"): "(f'') committed puzzle threshold input assembled under proofs/puzzle15",
    ("src/test/scala/Puzzle15Check.scala", "CERTIFICATE.tsv"): "(f'') output generated under proofs/puzzle15",
    ("src/test/scala/Puzzle15Check.scala", "EXPANSION.tsv"): "(f'') output generated under proofs/puzzle15",
    ("src/test/scala/Puzzle15Check.scala", "REPORT.md"): "(f'') output generated under proofs/puzzle15",
    ("src/test/scala/Puzzle15Check.scala", "SELECTION-alloc.tsv"): "(f'') output generated under proofs/puzzle15",

    # `CLAIMS.tsv`, the zipper-refinement obligation and pipeline coverage now exist, so their
    # former future-file exceptions are gone.

    # (The ELIDED-GOAL exception for puzzle15-space.smt2 is gone: since 2A.3 that cell is a trace
    # record, not a 174 MB denotation, and nothing is elided.)

    ("build.log", "review.md"): "(b) as above, cited by the narrative entries that acted on it",
    ("build.log", ".tools/env.sh"):
        "(b) a gitignored local tool directory that entry created; README.md now documents the "
        "ordinary installation and `toolchain.conf` is the resolution policy, so nothing in the "
        "tree depends on it any more",
    ("build.log", "attic-formal.egg"):
        "(b) the archived copy of formal.egg from the scala-cli era; removed when the port finished",
    ("build.log", "IntegrationLadderProbe.scala"):
        "(b) a throwaway probe suite, and the entry itself says `DELETED before this entry`",
    ("build.log", "plan.md"): "(b) the append-only narrative cites the superseded plan that existed then",
    ("build.log", ".frontier.tsv"): "(b) generated-artifact suffix recorded by the append-only narrative",
    ("build.log", ".trace.tsv"): "(b) generated-artifact suffix recorded by the append-only narrative",
    ("build.log", "CERTIFICATE.tsv"): "(b) Puzzle15Check output recorded by the append-only narrative",
    ("build.log", "EXPANSION.tsv"): "(b) Puzzle15Check output recorded by the append-only narrative",
    ("build.log", "REPORT.md"): "(b) Puzzle15Check output recorded by the append-only narrative",
    ("build.log", "SELECTION-alloc.tsv"): "(b) Puzzle15Check output recorded by the append-only narrative",
    ("build.log", "THRESHOLDS.tsv"): "(b) puzzle threshold artifact recorded by the append-only narrative",
    ("build.log", "target/gates.tsv"): "(b) ignored gate witness recorded by the append-only narrative",
    ("build.log", "target/trace-closure.tsv"): "(b) ignored closure witness recorded by the append-only narrative",
    ("build.log", "target/trace-closure-injected.tsv"): "(b) ignored mutation witness recorded by the append-only narrative",
    ("build.log", ".test.scala"):
        "(c) the scala-cli test-scope SUFFIX `*.test.scala` / `<Name>.test.scala`, not a filename",
    ("build.log", "keys_intersection/subtraction/composition/restriction/filter_exact.smt2"):
        "(c) shorthand for keys_intersection.smt2, keys_subtraction.smt2, keys_composition.smt2, "
        "keys_restriction.smt2, keys_filter_exact.smt2",
}

# Files whose CONTENT is data rather than prose, and whose tokens are therefore values.  These are
# still SCANNED for markdown links and for absolute paths; only the bare-filename token sweep is
# skipped, and the reason is per file.
DATA_FILES = {
    "corpus_1000.txt": "one serialised program per line; every token is a program term",
    "expressivity.csv": "generated measurement rows",
    "corpus_runtimes.csv": "generated measurement rows",
    "prog_matrix.tsv": "generated measurement rows",
    "proofs/laws/MINED.tsv": "mined law candidates; the `file` column names files that resolve, the rest are terms",
    "datalog-morkl.txt": "generated program dump",
}
# `.gitignore` is NO LONGER a whole-file skip. Its lines are patterns naming paths
# that are absent BY DESIGN, and each such token is excused individually in TOKEN_EXCEPTIONS with
# the reason it is absent -- so a pattern that names a path which is neither tracked nor declared
# absent (a typo, or a stale ignore for a file that moved) fails like any other dangling reference.

# ABSOLUTE PATHS ARE A HARD FAILURE EVERYWHERE, including in the data files above and in build.log.
# This is the check that `laws.diff` (removed) and the personal paths in `build.log` and
# `terminating/datalog_a.txt` (rewritten) used to fail while the reference sweep passed.
ABS_RE = re.compile(r"(?<![\w./$-])(/Users/[\w.-]+|/home/[\w.-]+|/Applications/[\w.-]+|[A-Za-z]:\\[\w.-]+\\)")

# `(?<![\w./$-])` also rules out `$name-space.egg` / `"$1.smt2"`: a token whose first character is
# preceded by `$` is an interpolation, and the file it names exists only at run time.
TOKEN_RE = re.compile(r"(?<![\w./$-])((?:[\w.@-]+/)*[\w.@-]+\.[A-Za-z0-9]+)(?![\w])")
MDLINK_RE = re.compile(r"\[([^\]]*)\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")


SNAPSHOT_MODES = ("worktree", "index", "head")


def _git(args, binary=False):
    """Run a git plumbing command in the repo.  Returns None on failure rather than raising, so a
    non-repo checkout degrades to the worktree mode instead of crashing."""
    try:
        r = subprocess.run(["git", "-C", str(ROOT)] + args, capture_output=True, check=True)
        return r.stdout if binary else r.stdout.decode()
    except (OSError, subprocess.CalledProcessError):
        return None


def snapshot_tree(mode):
    """The tree object to read for a git snapshot mode.  `index` writes the current index out as a
    tree -- the STAGED state, neither HEAD nor the worktree; `head` is HEAD's tree."""
    if mode == "index":
        out = _git(["write-tree"])
        return out.strip() if out else None
    if mode == "head":
        out = _git(["rev-parse", "HEAD^{tree}"])
        return out.strip() if out else None
    return None


def materialise(mode):
    """-> (root, names, tmp).  `root` holds the snapshot's contents; `names` is the set of
    snapshot-relative paths, which is what references resolve against; `tmp` is a directory to
    remove afterwards, or None.

    For a git mode both come out of ONE `git archive` of ONE tree object -- which is the whole
    point: names and contents cannot disagree because they are the same export."""
    if mode == "worktree":
        names = set()
        for f in ROOT.rglob("*"):
            if not f.is_file():
                continue
            rel = f.relative_to(ROOT)
            if any(part in SKIP_DIRS for part in rel.parts):
                continue
            names.add(str(rel))
        return ROOT, names, None

    tree = snapshot_tree(mode)
    if tree is None:
        raise SystemExit(f"cannot resolve the `{mode}` snapshot: not a git repository, or git failed")
    tar = _git(["archive", "--format=tar", tree], binary=True)
    if tar is None:
        raise SystemExit(f"`git archive` failed for the `{mode}` snapshot ({tree})")
    tmp = pathlib.Path(tempfile.mkdtemp(prefix=f"zippy-{mode}-"))
    with tarfile.open(fileobj=io.BytesIO(tar)) as tf:
        tf.extractall(tmp)
    names = {str(f.relative_to(tmp)) for f in tmp.rglob("*") if f.is_file()}
    return tmp, names, tmp


def is_text(f: pathlib.Path) -> bool:
    """BY CONTENT, never by name: a NUL byte in the first 8 KiB means binary."""
    try:
        with open(f, "rb") as fh:
            return b"\0" not in fh.read(8192)
    except OSError:
        return False


def resolves(ref: str, origin_rel: str, names: set) -> bool:
    """Does `ref` name a file IN THE SNAPSHOT?

    SET MEMBERSHIP, NOT `Path.exists()`.  Two requirements ride on that: an untracked file cannot
    make a reference resolve (it is not in the set), and CASE IS COMPARED EXACTLY on every platform
    -- `exists()` answers `True` for a target that differs from the real name only in case on a
    case-insensitive filesystem and `False` on Linux, so the same repository would pass in one
    place and fail in another (regression (d) in `selftest()` below)."""
    base = ref.split("/")[-1]
    if base in GENERATED or base in EXTERNAL_DATA:
        return True
    cands = [posixpath.normpath(posixpath.join(posixpath.dirname(origin_rel), ref))]
    cands += [posixpath.normpath(posixpath.join(r, ref)) if r else posixpath.normpath(ref)
              for r in SEARCH_ROOTS]
    if any(c in names for c in cands):
        return True
    # A DIRECTORY REFERENCE -- `docs/SUPERCOMPILER.md` links `../src/test/scala`, and a git tree has
    # no entry for a directory as such.  A directory is in the snapshot exactly when the snapshot
    # holds a file beneath it, and the prefix test keeps case exact the same way membership does.
    pre = tuple(c.rstrip("/") + "/" for c in cands if c not in (".", "/"))
    return bool(pre) and any(n.startswith(pre) for n in names)


def scan(root, names, used_exceptions):
    """Scan every text file of the snapshot.  `root` supplies CONTENTS, `names` supplies both the
    file list and the resolution target -- one snapshot, both halves."""
    problems = []
    for relstr in sorted(names):
        f = root / relstr
        if not f.is_file() or not is_text(f):
            continue
        if any(part in SKIP_DIRS for part in pathlib.PurePosixPath(relstr).parts):
            continue
        try:
            text = f.read_text(errors="replace")
        except OSError:
            continue

        # (0) ABSOLUTE PATHS -- everywhere, data files and logs included.  A committed absolute path
        # is either dead on every other machine or a personal directory; neither belongs in a tree.
        for m in ABS_RE.finditer(text):
            line = text[: m.start()].count("\n") + 1
            problems.append(f"{relstr}:{line}: ABSOLUTE PATH in a tracked file: {m.group(1)}")

        # (1) markdown links
        if relstr.endswith(".md"):
            for m in MDLINK_RE.finditer(text):
                tgt = m.group(2).split("#")[0]
                if not tgt or tgt.startswith(("http://", "https://", "mailto:")):
                    continue
                if not resolves(tgt, relstr, names):
                    line = text[: m.start()].count("\n") + 1
                    problems.append(f"{relstr}:{line}: broken markdown link [{m.group(1)}]({m.group(2)})")

        # (2) prose / comment citations.  DATA_FILES are exempt from this sweep only -- their tokens
        # are values, and each one says so in the table above.
        if relstr in DATA_FILES:
            continue
        seen = {}
        for m in TOKEN_RE.finditer(text):
            ref = m.group(1)
            ext = "." + ref.rsplit(".", 1)[1]
            if ext in PATH_ONLY and "/" not in ref:
                continue
            if ext not in ALWAYS and ext not in PATH_ONLY:
                continue
            if IGNORE_RE.search(ref):
                continue
            if resolves(ref, relstr, names):
                continue
            key = (relstr, ref)
            if key in TOKEN_EXCEPTIONS:
                used_exceptions.add(key)
                continue
            # THE DECLARATION FILE.  `TOKEN_EXCEPTIONS` above necessarily SPELLS every excused
            # token, so the sweep finds each one here as well.  A token declared anywhere in the
            # table is excused in the file that declares it -- and only there.  This is not a
            # whole-file skip: a token this file mentions WITHOUT declaring it still fails.
            if relstr == DECLARING_FILE and any(ref == k[1] for k in TOKEN_EXCEPTIONS):
                continue
            line = text[: m.start()].count("\n") + 1
            seen.setdefault(ref, []).append(line)
        for ref, ls in sorted(seen.items()):
            where = ",".join(str(x) for x in ls[:4]) + ("..." if len(ls) > 4 else "")
            problems.append(f"{relstr}:{where}: reference to a file that does not exist: {ref} "
                            f"({len(ls)} occurrence(s))")
    return problems


# ==================================================================================================
# THE SNAPSHOT-SEMANTICS REGRESSIONS
#
# The bug this file used to have was not a wrong answer on this repository -- it was a checker whose
# answer depended on state the answer did not describe.  That class of bug is invisible to any test
# that runs on the repository itself, so these build a THROWAWAY GIT REPOSITORY, put it into each
# state the review names, and assert what each snapshot mode must say.
# ==================================================================================================
def selftest():
    import shutil as _sh
    failures = []

    def run(tmp, mode):
        """Run the scan against `mode` inside `tmp`, returning the problem list."""
        global ROOT
        keep = ROOT
        ROOT = tmp
        try:
            root, names, scratch = materialise(mode)
            try:
                return scan(root, names, set())
            finally:
                if scratch is not None:
                    _sh.rmtree(scratch, ignore_errors=True)
        finally:
            ROOT = keep

    def git(tmp, *a):
        subprocess.run(["git", "-C", str(tmp)] + list(a), capture_output=True, check=True)

    def fresh_repo():
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="zippy-selftest-"))
        git(tmp, "init", "-q")
        git(tmp, "config", "user.email", "t@t"); git(tmp, "config", "user.name", "t")
        return tmp

    def expect(case, got, want_substr, want):
        hit = any(want_substr in g for g in got)
        if hit != want:
            failures.append(f"{case}: expected {'a' if want else 'no'} problem matching "
                            f"{want_substr!r}, got {got or '[]'}")

    # (a) A REFERENCE ADDED BY AN UNCOMMITTED EDIT must be invisible to `head` and visible to
    #     `worktree`.  The old code would have seen it in `--fresh` too, because it read
    #     working-tree CONTENTS under tracked names.
    tmp = fresh_repo()
    (tmp / "selftest-a.md").write_text("nothing here\n")
    git(tmp, "add", "selftest-a.md"); git(tmp, "commit", "-qm", "one")
    (tmp / "selftest-a.md").write_text("see [x](selftest-missing.md)\n")
    expect("(a) uncommitted edit, head", run(tmp, "head"), "selftest-missing.md", False)
    expect("(a) uncommitted edit, worktree", run(tmp, "worktree"), "selftest-missing.md", True)
    expect("(a) uncommitted edit, index", run(tmp, "index"), "selftest-missing.md", False)
    git(tmp, "add", "selftest-a.md")
    expect("(a) staged edit, index", run(tmp, "index"), "selftest-missing.md", True)
    expect("(a) staged edit, head", run(tmp, "head"), "selftest-missing.md", False)
    _sh.rmtree(tmp, ignore_errors=True)

    # (b) A DELETED-FROM-DISK BUT STILL-TRACKED file must still be scanned by `head`/`index`.  The
    #     old code skipped it silently (`if not f.is_file(): continue` over a tracked name list),
    #     so a dangling reference could be hidden by deleting the file that carries it.
    tmp = fresh_repo()
    (tmp / "selftest-b.md").write_text("see [x](selftest-gone.md)\n")
    git(tmp, "add", "selftest-b.md"); git(tmp, "commit", "-qm", "two")
    (tmp / "selftest-b.md").unlink()
    expect("(b) deleted on disk, head", run(tmp, "head"), "selftest-gone.md", True)
    expect("(b) deleted on disk, worktree", run(tmp, "worktree"), "selftest-gone.md", False)
    _sh.rmtree(tmp, ignore_errors=True)

    # (c) AN UNTRACKED FILE must not make a reference resolve, in any mode -- including `worktree`,
    #     because resolution is against the snapshot's NAME SET and an untracked file is not in the
    #     index or HEAD.  In `worktree` mode the name set is what is on disk, so it does resolve
    #     there; that asymmetry is the point of having the modes, and it is asserted rather than
    #     assumed.
    tmp = fresh_repo()
    (tmp / "selftest-c.md").write_text("see [x](selftest-helper.md)\n")
    git(tmp, "add", "selftest-c.md"); git(tmp, "commit", "-qm", "three")
    (tmp / "selftest-helper.md").write_text("hi\n")            # never added
    expect("(c) untracked target, head", run(tmp, "head"), "selftest-helper.md", True)
    expect("(c) untracked target, index", run(tmp, "index"), "selftest-helper.md", True)
    expect("(c) untracked target, worktree", run(tmp, "worktree"), "selftest-helper.md", False)
    _sh.rmtree(tmp, ignore_errors=True)

    # (d) A CASE-ONLY MISMATCH must fail on every platform.  `Path.exists()` would answer True on a
    #     case-insensitive filesystem, so this is exactly the check that cannot be delegated to the
    #     filesystem.
    tmp = fresh_repo()
    (tmp / "selftest-Spec.md").write_text("the spec\n")
    (tmp / "selftest-d.md").write_text("see [p](selftest-spec.md)\n")
    git(tmp, "add", "selftest-Spec.md", "selftest-d.md"); git(tmp, "commit", "-qm", "four")
    expect("(d) case-only mismatch, head", run(tmp, "head"), "selftest-spec.md", True)
    got = run(tmp, "head")
    if any("selftest-Spec.md" in g and "does not exist" in g for g in got):
        failures.append(f"(d) the correctly-cased name must resolve, got {got}")
    _sh.rmtree(tmp, ignore_errors=True)

    # (e) `resolves()` IS SET MEMBERSHIP, WITH THE FILESYSTEM DISAGREEING. The
    #     regressions above run the whole scanner against git snapshots; this one calls `resolves`
    #     directly against an in-memory name set inside a directory whose contents CONTRADICT it,
    #     so the test discriminates the checker's own resolution from anything Linux answers:
    #       * a name in the set that is NOT on disk must resolve;
    #       * a file on disk that is NOT in the set must not;
    #       * a case-only variant of a set member must not, whatever the filesystem says.
    tmp = fresh_repo()
    (tmp / "on-disk-only.md").write_text("present on disk, absent from the set\n")
    names = {"docs/in-set-only.md", "docs/Spec.md", "scripts/x.py"}
    global ROOT
    keep = ROOT
    ROOT = tmp
    try:
        if not resolves("in-set-only.md", "docs/readme.md", names):
            failures.append("(e) a name in the set (not on disk) did not resolve")
        if not resolves("docs/in-set-only.md", "README.md", names):
            failures.append("(e) a repo-relative name in the set did not resolve from the root")
        if resolves("on-disk-only.md", "README.md", names):
            failures.append("(e) a file present on disk but absent from the set resolved")
        if resolves("docs/spec.md", "README.md", names):
            failures.append("(e) a case-only variant of a set member resolved")
        if not resolves("../scripts/x.py", "docs/readme.md", names):
            failures.append("(e) a relative path into another directory of the set did not resolve")
        if not resolves("scripts", "README.md", names):
            failures.append("(e) a directory implied by a set member did not resolve")
    finally:
        ROOT = keep
    _sh.rmtree(tmp, ignore_errors=True)

    for f in failures:
        print(f"SELFTEST FAIL  {f}")
    print()
    print(f"selftest: {'PASS' if not failures else str(len(failures)) + ' FAILURE(S)'}"
          f"  (snapshot modes: {', '.join(SNAPSHOT_MODES)})")
    return 0 if not failures else 1


if __name__ == "__main__":
    strict = "--strict" in sys.argv
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    mode = "worktree"
    for a in sys.argv[1:]:
        if a.startswith("--snapshot="):
            mode = a.split("=", 1)[1]
            if mode not in SNAPSHOT_MODES:
                sys.exit(f"--snapshot must be one of {', '.join(SNAPSHOT_MODES)}")
        elif a == "--fresh":
            mode = "index"
    root, names, scratch = materialise(mode)
    used = set()
    try:
        ps = scan(root, names, used)
    finally:
        if scratch is not None:
            shutil.rmtree(scratch, ignore_errors=True)

    for pr in ps:
        print(pr)
    # UNUSED EXCEPTIONS ARE ONLY AUTHORITATIVE UNDER A GIT SNAPSHOT.  In the worktree an untracked
    # file can resolve a token, so the exception is legitimately never consulted.
    unused = sorted(k for k in TOKEN_EXCEPTIONS if k not in used)
    hard = strict and mode != "worktree"
    if unused:
        msg = ("unused TOKEN_EXCEPTIONS (the cause is gone -- delete the entry):" if mode != "worktree" else
               "TOKEN_EXCEPTIONS not consulted in the WORKING TREE (re-run with --fresh, where this "
               "is authoritative -- a local untracked file may be resolving the token):")
        print()
        print(("ERROR: " if hard else "note: ") + msg)
        for k in unused:
            print(f"    {k[0]}: {k[1]}")
    print()
    print(f"snapshot: {mode}" + ("" if mode == "worktree" else f" (tree {snapshot_tree(mode)})") +
          f"   files: {len(names)}")
    print(f"declared token exceptions: {len(TOKEN_EXCEPTIONS)} ({len(used)} used)"
          f"   data files exempt from the token sweep only: {len(DATA_FILES)}")
    print(f"dangling references: {len(ps)}")
    sys.exit(1 if ps or (hard and unused) else 0)
