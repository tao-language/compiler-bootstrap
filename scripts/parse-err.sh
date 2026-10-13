#!/usr/bin/env bash
# Render the parse/syntax errors of a .tao file (or inline expression) without
# the "Todo found" warning noise that otherwise buries them.
#
# Usage:
#   scripts/parse-err.sh path/to/file.tao
#   scripts/parse-err.sh -e "fn f(g: Int -> Num) = 1"
#
# The first form runs the file through `./tao check <file>`; the second
# runs an inline expression through `./tao run -e "<expr>"`.
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ "${1:-}" == "-e" ]]; then
  cmd=(./tao run -e "${2:?missing expression}")
else
  cmd=(./tao check "${1:?usage: parse-err.sh <file.tao> | -e <expr>}")
fi

# ./tao wraps the run in `timeout` (a hung BEAM ignores SIGTERM); TAO_TIMEOUT
# defaults to 5s here (margin over ./tao's 2s default) but the caller's value
# wins. Keep only the error summary + its trace lines, dropping the
# Todo-warning noise.
TAO_TIMEOUT="${TAO_TIMEOUT:-5}" "${cmd[@]}" 2>&1 \
  | grep -E '❌|^[[:space:]]+in "|syntax error' \
  || true
