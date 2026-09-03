#!/bin/sh
# EXTERNAL TOOL RESOLUTION for the shell drivers (proofs/run.sh, terminating/run.sh, ...).
#
# One of the three THIN ADAPTERS over `toolchain.conf`, which is the single policy: this file holds
# no tool name, no environment-variable name and NO INSTALL LOCATION -- it reads all of them.  The
# Python adapter is scripts/toolpath.py and the Scala adapter is src/main/scala/Tools.scala.
#
# Usage:
#   . "$(dirname "$0")/../scripts/toolpath.sh"
#   Z3_BIN=$(resolve_tool z3)       || { echo "$(tool_missing z3)" >&2; exit 1; }
#   VAMPIRE_BIN=$(resolve_tool vampire)
#
# `resolve_tool` prints the resolved path and returns 0, or prints nothing and returns 1.

# The policy file: $ZIPPY_TOOLCHAIN, else the nearest `toolchain.conf` at or above $PWD, else the
# one beside the sourcing script's parent directory.  `$0` is the CALLER when this file is sourced
# (that is the documented usage), so it is the fallback and not the primary lookup.
_toolpath_policy() {
  if [ -n "${ZIPPY_TOOLCHAIN:-}" ]; then echo "$ZIPPY_TOOLCHAIN"; return; fi
  _tp_d=$(pwd)
  while [ -n "$_tp_d" ]; do
    [ -f "$_tp_d/toolchain.conf" ] && { echo "$_tp_d/toolchain.conf"; return; }
    [ "$_tp_d" = "/" ] && break
    _tp_d=$(dirname -- "$_tp_d")
  done
  _tp_up=$(CDPATH= cd -- "$(dirname -- "${1:-scripts/toolpath.sh}")/.." 2>/dev/null && pwd)
  [ -n "$_tp_up" ] && echo "$_tp_up/toolchain.conf" || echo toolchain.conf
}
_TOOLPATH_CONF=$(_toolpath_policy "$0")

# `search = ...` from the policy, or the location-free fallback when the file is absent.
_toolpath_search() {
  _tp_s=$(sed -n 's/[#].*//; s/^[[:space:]]*search[[:space:]]*=[[:space:]]*//p' "$_TOOLPATH_CONF" 2>/dev/null \
            | head -1 | tr -d ' ' | tr ',' ' ')
  [ -n "$_tp_s" ] && echo "$_tp_s" || echo "env path"
}

# One key of one tool's [section] in the policy; empty when absent.
_toolpath_key() {
  awk -v want="$1" -v key="$2" '
    { sub(/#.*/, "") }
    /^[[:space:]]*\[/ { gsub(/[][[:space:]]/, ""); sect = $0; next }
    sect == want && $0 ~ ("^[[:space:]]*" key "[[:space:]]*=") {
      sub(/^[^=]*=[[:space:]]*/, ""); gsub(/[[:space:]]+$/, ""); print; exit }
  ' "$_TOOLPATH_CONF" 2>/dev/null
}

_toolpath_binary() { _tp_b=$(_toolpath_key "$1" binary); [ -n "$_tp_b" ] && echo "$_tp_b" || echo "$1"; }
_toolpath_envvar() {
  _tp_v=$(_toolpath_key "$1" env)
  [ -n "$_tp_v" ] && echo "$_tp_v" || echo "$1" | tr '[:lower:]' '[:upper:]'
}

resolve_tool() {
  _tp_name="$1"
  _tp_bin=$(_toolpath_binary "$_tp_name")
  _tp_var=$(_toolpath_envvar "$_tp_name")
  for _tp_step in $(_toolpath_search); do
    case "$_tp_step" in
      env)
        _tp_env=$(eval "printf '%s' \"\${$_tp_var:-}\"")
        if [ -n "$_tp_env" ]; then
          case "$_tp_env" in
            */*) [ -x "$_tp_env" ] && { echo "$_tp_env"; return 0; } ;;
            *)   command -v "$_tp_env" >/dev/null 2>&1 && { command -v "$_tp_env"; return 0; } ;;
          esac
        fi ;;
      zippy-tools)
        if [ -n "${ZIPPY_TOOLS:-}" ] && [ -x "$ZIPPY_TOOLS/$_tp_bin" ]; then
          echo "$ZIPPY_TOOLS/$_tp_bin"; return 0
        fi ;;
      path)
        command -v "$_tp_bin" >/dev/null 2>&1 && { command -v "$_tp_bin"; return 0; } ;;
      elan)
        # elan's own root, from its documented $ELAN_HOME override or its documented default.  See
        # toolchain.conf's header for why `lake` cannot be found the way a prover is.
        _tp_elan="${ELAN_HOME:-$HOME/.elan}/bin/$_tp_bin"
        [ -x "$_tp_elan" ] && { echo "$_tp_elan"; return 0; } ;;
    esac
  done
  return 1
}

tool_missing() {
  _tp_name="$1"
  _tp_bin=$(_toolpath_binary "$_tp_name")
  _tp_var=$(_toolpath_envvar "$_tp_name")
  echo "$_tp_name not found: set \$$_tp_var to its path, put \`$_tp_bin\` on PATH, or point \$ZIPPY_TOOLS at the directory holding it (policy: $(basename "$_TOOLPATH_CONF"), search order: $(_toolpath_search | tr ' ' ','))"
}
