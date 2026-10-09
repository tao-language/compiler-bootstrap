#!/bin/bash
# Run the tao compiler from a given directory
# Usage: scripts/run_from.sh <dir> <args...>
DIR="$1"
shift
cd "$DIR" || exit 1
ERL_PATHS=""
for pkg in compiler_bootstrap gleam_stdlib simplifile filepath argv glam nibble gleam_regexp gflambe gleam_erlang iv; do
  ERL_PATHS="$ERL_PATHS -pa /Users/david/src/compiler-bootstrap/build/dev/erlang/$pkg/ebin"
done
# Convert remaining args to an Erlang list of binaries using list_to_binary
ARGS=""
for arg in "$@"; do
  ESCAPED=$(echo "$arg" | sed 's/"/\\"/g')
  if [ -n "$ARGS" ]; then
    ARGS="$ARGS, list_to_binary(\"$ESCAPED\")"
  else
    ARGS="list_to_binary(\"$ESCAPED\")"
  fi
done
erl -noshell $ERL_PATHS -eval "
  Args = [$ARGS],
  'cli@entrypoint':entrypoint(Args),
  init:stop().
" 2>&1
