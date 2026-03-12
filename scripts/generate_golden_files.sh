#!/bin/bash
# Generate golden files for all examples

set -e

cd "$(dirname "$0")/.."

echo "Generating golden files for programs/..."
for file in examples/core/programs/*.core.tao; do
    name=$(basename "$file" .core.tao)
    output="examples/core/programs/${name}.output.txt"
    echo "  $name"
    gleam run run "$file" 2>/dev/null | grep -E "^(✓|Result:)" > "$output" || true
done

echo "Generating golden files for terms/..."
for file in examples/core/terms/*.core.tao; do
    name=$(basename "$file" .core.tao)
    output="examples/core/terms/${name}.output.txt"
    echo "  $name"
    gleam run run "$file" 2>/dev/null | grep -E "^(✓|Result:)" > "$output" || true
done

echo "Generating golden files for errors/type_errors/..."
for file in examples/core/errors/type_errors/*.core.tao; do
    name=$(basename "$file" .core.tao)
    output="examples/core/errors/type_errors/${name}.output.txt"
    echo "  $name"
    gleam run check "$file" 2>&1 | grep -v "^warning" | grep -v "^   " | grep -v "^Hint" | grep -v "^This" | grep -v "^It" | grep -v "^See" | grep -v "^$" | grep -v "^Compiled" | grep -v "^    Running" > "$output" || true
done

echo "Done!"
