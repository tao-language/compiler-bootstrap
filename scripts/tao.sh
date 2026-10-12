#!/bin/bash
# Run the tao compiler CLI. Pass all args through, e.g.:
#   scripts/tao.sh test /tmp/fn_type.tao
#   scripts/tao.sh run -e "Int -> Num" --trace resolve
#
# stderr is captured and shown only on failure (the common case is just
# `todo` build warnings, which are noise). Override the timeout with
# TAO_TIMEOUT (default 5s; --trace defines/holes print the whole prelude
# context and may need TAO_TIMEOUT=20).
set -uo pipefail
cd "$(dirname "$0")/.."
tmp_err=$(mktemp)
timeout -k 9 "${TAO_TIMEOUT:-5}" gleam run -- "$@" 2>"$tmp_err"
status=$?
if [ $status -ne 0 ] && [ -s "$tmp_err" ]; then
  grep -vE "warning: Todo|┌|└|│|\^|This code will crash|running your program|Hint: I think|^$" "$tmp_err" | head -30
fi
rm -f "$tmp_err"
exit $status
