#!/usr/bin/env python3
"""EXTERNAL TOOL RESOLUTION for the Python generators/checkers.

The Python twin of src/main/scala/Tools.scala and scripts/toolpath.sh: same environment
variables, same conventional locations, same order.

  1. $Z3 / $VAMPIRE / $EGGLOG   (an absolute path, or a name on PATH)
  2. PATH
  3. a short conventional-location list
  4. otherwise None -- and the caller must SAY the tool is missing rather than skip silently.

  from toolpath import resolve, missing_message
  z3 = resolve("z3")
  if z3 is None:
      sys.exit(missing_message("z3"))
"""
import os
import shutil

ENV_VAR = {"z3": "Z3", "vampire": "VAMPIRE", "egglog": "EGGLOG"}

CONVENTIONAL = {
    "z3": ["/usr/local/bin/z3", "/opt/homebrew/bin/z3", "~/.local/bin/z3"],
    "vampire": ["/usr/local/bin/vampire", "/opt/homebrew/bin/vampire", "~/.local/bin/vampire"],
    "egglog": ["~/.cargo/bin/egglog", "/usr/local/bin/egglog", "/opt/homebrew/bin/egglog"],
}


def resolve(name):
    """The resolved executable path, or None."""
    var = ENV_VAR.get(name, name.upper())
    override = (os.environ.get(var) or "").strip()
    if override:
        if os.sep in override:
            if os.access(override, os.X_OK):
                return override
        else:
            found = shutil.which(override)
            if found:
                return found
    found = shutil.which(name)
    if found:
        return found
    for c in CONVENTIONAL.get(name, []):
        c = os.path.expanduser(c)
        if os.access(c, os.X_OK):
            return c
    return None


def missing_message(name):
    var = ENV_VAR.get(name, name.upper())
    tried = ", ".join(CONVENTIONAL.get(name, []))
    return (f"{name} not found: set ${var} to its path, or put `{name}` on PATH "
            f"(also tried: {tried})")


if __name__ == "__main__":
    for t in ("z3", "vampire", "egglog"):
        print(f"{t:8s} {resolve(t) or 'ABSENT'}")
