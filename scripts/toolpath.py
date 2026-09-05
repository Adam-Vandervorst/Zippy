#!/usr/bin/env python3
"""EXTERNAL TOOL RESOLUTION for the Python generators/checkers.

One of the three THIN ADAPTERS over `toolchain.conf`, which is the single policy: this file holds
no tool name, no environment-variable name and NO INSTALL LOCATION -- it reads all of them.  The
`sh` adapter is scripts/toolpath.sh and the Scala adapter is src/main/scala/Tools.scala.

  from toolpath import resolve, missing_message
  z3 = resolve("z3")
  if z3 is None:
      sys.exit(missing_message("z3"))
"""
import os
import pathlib
import shutil

# The policy file: $ZIPPY_TOOLCHAIN, else `toolchain.conf` at the repo root.
POLICY_PATH = pathlib.Path(
    os.environ.get("ZIPPY_TOOLCHAIN")
    or (pathlib.Path(__file__).resolve().parent.parent / "toolchain.conf")
)

DEFAULT_SEARCH = ["env", "path"]   # the location-free fallback when the policy file is absent


def _parse(path):
    """-> (search_order, {tool: {key: value}}).  A 3-line ini reader; no dependency."""
    search, tools, cur = list(DEFAULT_SEARCH), {}, None
    try:
        text = path.read_text()
    except OSError:
        return search, tools
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("[") and line.endswith("]"):
            cur = line[1:-1].strip()
            tools.setdefault(cur, {})
            continue
        if "=" not in line:
            continue
        k, v = (x.strip() for x in line.split("=", 1))
        if cur is None:
            if k == "search":
                search = [s.strip() for s in v.split(",") if s.strip()]
        else:
            tools[cur][k] = v
    return search, tools


SEARCH, TOOLS = _parse(POLICY_PATH)


def _spec(name):
    """The policy entry for `name`, defaulted so an unlisted tool still resolves via env+PATH."""
    s = dict(TOOLS.get(name, {}))
    s.setdefault("binary", name)
    s.setdefault("env", name.upper())
    return s


def names():
    """Every tool the policy declares, in file order."""
    return list(TOOLS)


def resolve(name):
    """The resolved executable path, or None.  Steps and order come from the policy's `search`."""
    spec = _spec(name)
    binary = spec["binary"]
    for step in SEARCH:
        if step == "env":
            override = (os.environ.get(spec["env"]) or "").strip()
            if not override:
                continue
            if os.sep in override:
                if os.access(override, os.X_OK):
                    return override
            else:
                found = shutil.which(override)
                if found:
                    return found
        elif step == "zippy-tools":
            root = (os.environ.get("ZIPPY_TOOLS") or "").strip()
            if root:
                cand = os.path.join(os.path.expanduser(root), binary)
                if os.access(cand, os.X_OK):
                    return cand
        elif step == "path":
            found = shutil.which(binary)
            if found:
                return found
        elif step == "elan":
            # elan's own root, from its documented $ELAN_HOME override or its documented default.
            # See toolchain.conf's header for why `lake` cannot be found the way a prover is.
            root = os.environ.get("ELAN_HOME") or os.path.join(os.path.expanduser("~"), ".elan")
            cand = os.path.join(root, "bin", binary)
            if os.access(cand, os.X_OK):
                return cand
    return None


def missing_message(name):
    spec = _spec(name)
    return (f"{name} not found: set ${spec['env']} to its path, put `{spec['binary']}` on PATH, "
            f"or point $ZIPPY_TOOLS at the directory holding it "
            f"(policy: {POLICY_PATH.name}, search order: {', '.join(SEARCH)})")


if __name__ == "__main__":
    for t in names() or ("z3", "vampire", "egglog"):
        print(f"{t:8s} {resolve(t) or 'ABSENT'}")
