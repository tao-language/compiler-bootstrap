#!/usr/bin/env bash
# Run `gleam build` and print a categorized table of warnings.
# Usage: scripts/warnings.sh
set -euo pipefail
cd "$(dirname "$0")/.."

OUT=$(mktemp)
timeout -k 9 5 gleam build > "$OUT" 2>&1 || true

echo "== $(grep -c '^warning:' "$OUT") warnings =="
echo
printf '%-32s %s\n' "KIND" "LOCATION"
awk '
/^warning:/ { type=$0; sub(/^warning: /,"",type) }
/┌─/ { loc=$0; sub(/.*┌─ /,"",loc); sub(/ *$/,"",loc); gsub("/Users/david/src/compiler-bootstrap/","",loc) ; print type " || " loc }
' "$OUT" | sort -t'|' -k3 | awk -F' \\|\\| ' '{ printf "%-32s %s\n", $1, $2 }'
echo
echo "== by kind =="
grep '^warning:' "$OUT" | sed 's/^warning: //' | sort | uniq -c | sort -rn
rm -f "$OUT"
