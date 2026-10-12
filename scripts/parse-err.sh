#!/usr/bin/env bash
# Render the parse/syntax errors of a .tao file (or inline expression) without
# the "Todo found" warning noise that otherwise buries them.
#
# Usage:
#   scripts/parse-err.sh path/to/file.tao
#   scripts/parse-err.sh -e "fn f(g: Int -> Num) = 1"
#
# The first form runs the file through `gleam run -- check <file>`; the second
# runs an inline expression through `gleam run -- run -e "<expr>"`.
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ "${1:-}" == "-e" ]]; then
  cmd=(gleam run -- run -e "${2:?missing expression}")
else
  cmd=(gleam run -- check "${1:?usage: parse-err.sh <file.tao> | -e <expr>}")
fi

# Run with a hard timeout (a hung BEAM ignores SIGTERM) and keep only the
# error summary + its trace lines, dropping the Todo-warning noise.
timeout -k 9 5 "${cmd[@]}" 2>&1 \
  | grep -E '❌|^[[:space:]]+in "|syntax error' \
  || true
