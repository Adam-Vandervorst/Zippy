#!/bin/sh
# EXTERNAL TOOL RESOLUTION for the shell drivers (proofs/run.sh, terminating/run.sh, ...).
# The `sh` twin of src/main/scala/Tools.scala and scripts/toolpath.py: same env variables, same
# conventional locations, same order.
#
#   1. $Z3 / $VAMPIRE / $EGGLOG            (an absolute path or a name on PATH)
#   2. PATH
#   3. a short conventional-location list
#   4. otherwise: empty, and the caller must SAY the tool is missing — never skip silently.
#
# Usage:
#   . "$(dirname "$0")/../scripts/toolpath.sh"
#   Z3_BIN=$(resolve_tool z3)       || { echo "$(tool_missing z3)" >&2; exit 1; }
#   VAMPIRE_BIN=$(resolve_tool vampire)
#
# `resolve_tool` prints the resolved path and returns 0, or prints nothing and returns 1.

_toolpath_conventional() {
  case "$1" in
    z3)      echo "/usr/local/bin/z3 /opt/homebrew/bin/z3 $HOME/.local/bin/z3" ;;
    vampire) echo "/usr/local/bin/vampire /opt/homebrew/bin/vampire $HOME/.local/bin/vampire" ;;
    egglog)  echo "$HOME/.cargo/bin/egglog /usr/local/bin/egglog /opt/homebrew/bin/egglog" ;;
    *)       echo "" ;;
  esac
}

_toolpath_env() {
  case "$1" in
    z3)      echo "${Z3:-}" ;;
    vampire) echo "${VAMPIRE:-}" ;;
    egglog)  echo "${EGGLOG:-}" ;;
    *)       echo "" ;;
  esac
}

resolve_tool() {
  _tp_name="$1"
  _tp_env=$(_toolpath_env "$_tp_name")
  if [ -n "$_tp_env" ]; then
    case "$_tp_env" in
      */*) [ -x "$_tp_env" ] && { echo "$_tp_env"; return 0; } ;;
      *)   command -v "$_tp_env" >/dev/null 2>&1 && { command -v "$_tp_env"; return 0; } ;;
    esac
  fi
  command -v "$_tp_name" >/dev/null 2>&1 && { command -v "$_tp_name"; return 0; }
  for _tp_c in $(_toolpath_conventional "$_tp_name"); do
    [ -x "$_tp_c" ] && { echo "$_tp_c"; return 0; }
  done
  return 1
}

tool_missing() {
  _tp_name="$1"
  case "$_tp_name" in
    z3)      _tp_var=Z3 ;;
    vampire) _tp_var=VAMPIRE ;;
    egglog)  _tp_var=EGGLOG ;;
    *)       _tp_var=$(echo "$_tp_name" | tr '[:lower:]' '[:upper:]') ;;
  esac
  echo "$_tp_name not found: set \$$_tp_var to its path, or put \`$_tp_name\` on PATH (also tried: $(_toolpath_conventional "$_tp_name"))"
}
