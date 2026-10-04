#!/usr/bin/env bash
# shape_matrix.sh — run the canonical result.tao-hang shape matrix with
# timeouts and print a pass/hang table (docs/plan.md §5/§10).
#
# Shapes (fresh names so prelude collisions are ruled out):
#   B — 2 params, 2 tests (the hang shape)
#   A — 1 param, 2 tests (control)
#   C — 2 params, 1 test  (control)
#
# Usage: scripts/shape_matrix.sh [TIMEOUT_S]
set -u
cd "$(dirname "$0")/.."
T="${1:-3}"
DIR=/tmp/taoscratch
mkdir -p "$DIR"

# Recreate the canonical shapes if missing.
[ -f "$DIR/B_two_params_two_tests.tao" ] || cat > "$DIR/B_two_params_two_tests.tao" <<'EOF'
type Rst(value, error) {
| OkX(value)
| ErrX(error)
}

fn _orx<a, e>(r: Rst(a, e), d: a) -> a
= match r {
| OkX(value) => value
| ErrX(_) => d
}

>>> _orx(OkX(10), 20)   10
>>> _orx(ErrX(10), 20)  20
EOF
[ -f "$DIR/A_one_param_two_tests.tao" ] || cat > "$DIR/A_one_param_two_tests.tao" <<'EOF'
type Optx(a) {
| SomeX(a)
| NoneX
}

fn _orx<a>(o: Optx(a), d: a) -> a
= match o {
| SomeX(x) => x
| NoneX => d
}

>>> _orx(SomeX(10), 20)  10
>>> _orx(NoneX, 20)      20
EOF
[ -f "$DIR/C_two_params_one_test.tao" ] || cat > "$DIR/C_two_params_one_test.tao" <<'EOF'
type Rst(value, error) {
| OkX(value)
| ErrX(error)
}

fn _orx<a, e>(r: Rst(a, e), d: a) -> a
= match r {
| OkX(value) => value
| ErrX(_) => d
}

>>> _orx(OkX(10), 20)   10
EOF

run() {
  local label="$1" file="$2"
  local out="/tmp/shape_matrix_$(basename "$file" .tao).out"
  # Subshell with stderr discarded: hides the "Killed: 9" job message.
  (
    timeout -k 9 "$T" gleam run -- test "$file" > "$out" 2>&1
    exit $?
  ) 2>/dev/null
  local code=$?
  pkill -9 -f beam.smp 2>/dev/null
  case $code in
    0)  echo "  PASS   $label ($file)" ;;
    1)  echo "  FAIL   $label ($file) — tests failed; see $out" ;;
    124|137) echo "  HANG   $label ($file) — killed after ${T}s" ;;
    *)  echo "  ERROR  $label ($file) — exit $code" ;;
  esac
}

echo "=== shape matrix (timeout ${T}s) ==="
run "2-param 2-test (hang shape)" "$DIR/B_two_params_two_tests.tao"
run "1-param 2-test (control)"    "$DIR/A_one_param_two_tests.tao"
run "2-param 1-test (control)"    "$DIR/C_two_params_one_test.tao"
run "prelude result.tao (target)" lib/prelude/v0.0.1/result.tao
run "prelude option.tao (control)" lib/prelude/v0.0.1/option.tao
exit 0
