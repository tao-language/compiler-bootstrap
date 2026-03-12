#!/bin/bash
# Generate golden files for all E2E test examples
# 
# Usage: ./scripts/generate_golden_files.sh
#
# This script:
# 1. Runs each .core.tao file through the compiler
# 2. Captures the output (stdout for success, stderr for errors)
# 3. Strips ANSI codes for portable golden files
# 4. Writes to corresponding .output.txt file

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_DIR"

echo "Generating golden files for E2E tests..."
echo ""

# Function to strip ANSI codes
strip_ansi() {
  sed 's/\x1b\[[0-9;]*m//g'
}

# Function to extract just the compiler output (skip build warnings)
extract_compiler_output() {
  # Skip everything before and including "Running compiler_bootstrap.main"
  # Keep only the actual program output
  sed '1,/Running compiler_bootstrap\.main/d'
}

# Generate golden files for successful programs
echo "=== Programs ==="
for file in examples/core/programs/*.core.tao; do
  if [ -f "$file" ]; then
    output="${file%.core.tao}.output.txt"
    echo "Generating: $output"
    gleam run run "$file" 2>&1 | strip_ansi | extract_compiler_output > "$output"
  fi
done

echo ""
echo "=== Terms ==="
for file in examples/core/terms/*.core.tao; do
  if [ -f "$file" ]; then
    output="${file%.core.tao}.output.txt"
    echo "Generating: $output"
    gleam run run "$file" 2>&1 | strip_ansi | extract_compiler_output > "$output"
  fi
done

echo ""
echo "=== Type Errors ==="
for file in examples/core/errors/type_errors/*.core.tao; do
  if [ -f "$file" ]; then
    output="${file%.core.tao}.output.txt"
    echo "Generating: $output"
    gleam run check "$file" 2>&1 | strip_ansi | extract_compiler_output > "$output"
  fi
done

echo ""
echo "=== Syntax Errors ==="
for file in examples/core/errors/syntax_errors/*.core.tao; do
  if [ -f "$file" ]; then
    output="${file%.core.tao}.output.txt"
    echo "Generating: $output"
    gleam run check "$file" 2>&1 | strip_ansi | extract_compiler_output > "$output"
  fi
done

echo ""
echo "=== Syntax Recovery ==="
for file in examples/core/errors/syntax_recovery/*.core.tao; do
  if [ -f "$file" ]; then
    output="${file%.core.tao}.output.txt"
    echo "Generating: $output"
    gleam run check "$file" 2>&1 | strip_ansi | extract_compiler_output > "$output"
  fi
done

echo ""
echo "=== Exhaustiveness Checks ==="
for file in examples/core/errors/exhaustiveness_checks/*.core.tao; do
  if [ -f "$file" ]; then
    output="${file%.core.tao}.output.txt"
    echo "Generating: $output"
    gleam run check "$file" 2>&1 | strip_ansi | extract_compiler_output > "$output"
  fi
done

echo ""
echo "✅ Golden file generation complete!"
echo ""
echo "Review the changes with: git diff examples/core/"
