#!/usr/bin/env bash
# Re-apply the meck 0.9.2 patch needed to compile under OTP 27+.
# meck's prod profile sets warnings_as_errors, and OTP 27+ deprecates the
# old `catch` expression, so a clean build of build/packages/meck fails.
# Run after any `rm -rf build` (or `gleam build` from scratch).
# Usage: scripts/fix-meck.sh
set -euo pipefail
cd "$(dirname "$0")/.."

FILE=build/packages/meck/rebar.config
if [ ! -f "$FILE" ]; then
  echo "meck not extracted yet; run 'gleam build' once first" >&2
  exit 1
fi
if grep -q nowarn_deprecated_catch "$FILE"; then
  echo "meck already patched"
else
  # Insert the suppression directive into the prod profile's erl_opts.
  perl -0pi -e 's/(\{prod, \[\n\s*\{erl_opts, \[\n\s*debug_info,\n)/$1            nowarn_deprecated_catch,\n/' "$FILE"
  grep -q nowarn_deprecated_catch "$FILE" && echo "meck patched"
fi
