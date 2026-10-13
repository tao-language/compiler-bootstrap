#!/usr/bin/env bash
# Smoke test for the tao CLI: exercises every main command, the -e/-s
# inputs, and every --trace kind. Exits non-zero on the first failure.
#
#   scripts/cli-smoke.sh
set -uo pipefail
cd "$(dirname "$0")/.."

pass=0
fail=0

# run <expected-grep> -- args...: runs `./tao args`, greps stdout+stderr
# for expected-grep, and checks the exit status matches $WANT (default 0).
check() {
  local want_grep="$1"; shift
  local want=0
  if [[ "${1:-}" == "--exit" ]]; then want="$2"; shift 2; fi
  local out
  # TAO_TIMEOUT=10: some checks trace the whole prelude and exceed ./tao's
  # 2s default; a caller-set TAO_TIMEOUT wins.
  out=$(TAO_TIMEOUT="${TAO_TIMEOUT:-10}" ./tao "$@" 2>&1)
  local status=$?
  local ok=1
  if [[ $status -ne 0 && $status -ne 124 && $want -eq 0 ]]; then ok=0; fi
  if [[ $want -ne 0 && $status -eq 0 ]]; then ok=0; fi
  if ! grep -qF "$want_grep" <<<"$out"; then ok=0; fi
  if [[ $ok -eq 1 ]]; then
    pass=$((pass+1))
    echo "ok   $*"
  else
    fail=$((fail+1))
    echo "FAIL $*  (status=$status, wanted grep: $want_grep)"
    grep -vE "warning: Todo|┌|└|│|\^|This code will crash|running your program|Hint: I think|Compiled in|Running compiler" <<<"$out" | head -15
  fi
}

# Inputs
check "2"                          run -e '1 + 1'
check "x = 1"                      run -s 'let x = 1
let y = 2'
check "y = 2"                      run -s 'let x = 1; let y = 2'
smoke_file=$(mktemp -d)/smoke.tao
printf 'let x = 1\n' > "$smoke_file"
check "x = 1"                      run "$smoke_file"

# check
check "expected" --exit 1          check -e 'let x ='
check "no such file" --exit 1      check missing-file.tao

# test
check "1 passed"                   test -s 'let x = 1
>>> x 1'
check "0 total"                    test -s 'let x = 1'
check "1 failed" --exit 1          test -s '>>> 1 2'

# per-file restriction
check "0 total"                    test test/cli/data/f1.tao:nonexistent

# traces
check ">> lex -> tokens"           check -e '1' --trace parse
check "FAILED (" --exit 1          check -e 'let x =' --trace parse
check "MODULE TRACE"               run -e '1' --trace modules
check "define.types:"              run -e '1' --trace defines
check "holes (after define)"       run -e '1' --trace holes
check "BUDGET used="               run -e '1' --trace solves
check "// desugar __result"        run -e '1 + 1' --trace desugar
check "// infer __result"          run -e '1 + 1' --trace infer
check "// resolve __result"        run -e '1 + 1' --trace resolve
check "// eval __result"           run -e '1 + 1' --trace eval
check "term:"                       test -s '>>> 1 1' --trace tests
check "PI (envlen="                 test -s 'fn f(x) = x' --dump-def f

# flags
check "unknown flag" --exit 1      run -e '1' --frobnicate
check "cannot mix" --exit 1        run test/cli/data/f1.tao -e '1'
check "cannot combine" --exit 1    run -e '1' -s 'let x = 1'
check "unknown trace kind" --exit 1 run --trace wibbles
check "missing value for --expr" --exit 1 run -e
check "only supported by test" --exit 1 check --filter foo

# help
check "Usage:"                     --help

echo ""
echo "cli-smoke: $pass passed, $fail failed"
[[ $fail -eq 0 ]]
