# Examples Testing Specification

> **Goal**: Define how examples are tested end-to-end with CLI integration
> **Status**: 📋 Planned
> **Date**: March 11, 2026

---

## Overview

All examples in the `examples/` directory should be tested. These examples should showcase the end-to-end usage of the CLI compiler.

---

## CLI Commands

### `check` Command

Type checking and exhaustiveness checks.

**Behavior**:
- Parse the source file
- Run type inference
- Run exhaustiveness checking
- Output formatted errors to `stderr` if any
- Return exit code `1` if errors found, `0` otherwise

**Usage**:
```bash
gleam run -- check examples/core/example.core.tao
```

### `run` Command

Type checking, exhaustiveness checks, and evaluation.

**Behavior**:
- Parse the source file
- Run type inference
- Run exhaustiveness checking
- Output formatted errors to `stderr` if any
- **Always** output the NbE normalized term to `stdout` (regardless of errors)
- Return exit code `1` if errors found, `0` otherwise

**Usage**:
```bash
gleam run -- run examples/core/example.core.tao
```

**Rationale**: Even with type errors, the term may still evaluate to a meaningful result. Showing the result helps with debugging.

---

## Success Example

### Source File

**File**: `examples/core/i32_add.core.tao`

```gleam
%call i32_add(1, 2)
```

### Expected Output

**File**: `examples/core/i32_add.output.txt`

```
3
```

This should be the exact same output as running:
```bash
gleam run -- run examples/core/i32_add.core.tao
```

---

## Failure Example

### Source File

**File**: `examples/core/errors/type_errors/type_mismatch.core.tao`

```gleam
// This type annotation doesn't match the value's type.
1 : $Type
```

### Expected Output

**File**: `examples/core/errors/type_errors/type_mismatch.output.txt`

```
❌ error[E0101]: Type mismatch
   ┌─ examples/core/errors/type_errors/type_mismatch.core.tao:2:5
   │
 1 │ // This type annotation doesn't match the value's type.
 2 │ 1 : $Type
   │     ^~~~~ value is Int, but it should be $Type
   │
   💡 The value 1 is of type Int
   💡 The type annotation expects a value of type $Type
   📝 note: Int and $Type are incompatible types
   🔧 help: Did you mean? `1 : Int`
-----------------------------------------------------------
1
```

This should be the exact same output as running:
```bash
gleam run -- run examples/core/errors/type_errors/type_mismatch.core.tao
```

**Notes**:
- Error output goes to `stderr`
- Result output goes to `stdout`
- Horizontal line (`---`) separates errors from result
- Exit code is `1` (errors were found)

---

## Error Output Format

### Code Snippets

Code snippets should display:
- **2-3 lines before** the error location for context
- **The error line** with pointer to the specific location
- **2-3 lines after** for additional context

**Example**:
```
   ┌─ examples/core/errors/type_errors/type_mismatch.core.tao:2:5
   │
 1 │ // This type annotation doesn't match the value's type.
 2 │ 1 : $Type
   │     ^~~~~ value is Int, but it should be $Type
 3 │ 
 4 │ // More context if needed
   │
```

### Error Components

1. **Header**: `❌ error[E####]: Error category`
2. **Duplicate header**: `error[E####]: Error message` (for terminal visibility)
3. **Source span**: `┌─ file:line:col`
4. **Source snippet**: With line numbers and pointer
5. **Inline message**: Next to pointer explaining the issue
6. **Notes**: Additional context (`💡`, `📝`)
7. **Help**: Suggestions for fixing (`🔧`)

### Delimiter

A horizontal line separates errors from the result:
```
-----------------------------------------------------------
```

---

## Test Implementation

### Test Structure

```gleam
pub fn examples_test() {
  "examples/core"
  |> discover_examples
  |> list.each(run_example_test)
}

fn run_example_test(example: Example) {
  let expected = read_file(example.output_path)
  let actual = run_cli(example.path)
  
  case normalize(actual) == normalize(expected) {
    True -> pass()
    False -> fail(expected, actual)
  }
}
```

### CLI Execution

```gleam
fn run_cli(path: String) -> String {
  // Run: gleam run -- run <path>
  // Capture both stdout and stderr
  // Combine in order: stderr (errors) + delimiter + stdout (result)
}
```

### Normalization

For comparison, normalize:
- Strip ANSI color codes
- Trim trailing whitespace
- Normalize line endings

**Do NOT normalize**:
- Error codes
- Line numbers
- Column numbers
- Error messages

---

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success (no errors) |
| 1 | Errors found (type errors, parse errors, exhaustiveness errors) |
| 2 | Runtime error |
| 3 | File not found |
| 4 | Invalid arguments |

---

## Golden File Generation

### Script

```bash
#!/bin/bash
# scripts/generate_golden_files.sh

for file in examples/core/**/*.core.tao; do
  output="${file%.core.tao}.output.txt"
  gleam run -- run "$file" > "$output" 2>&1
done
```

### Manual Generation

```bash
# Single file
gleam run -- run examples/core/example.core.tao > examples/core/example.output.txt 2>&1

# Error example
gleam run -- run examples/core/errors/type_errors/example.core.tao > examples/core/errors/type_errors/example.output.txt 2>&1
```

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Testing overview
- **[02-e2e-test-enhancement.md](./02-e2e-test-enhancement.md)** - E2E test implementation
- **[../cli/01-overview.md](../cli/01-overview.md)** - CLI overview
- **[../cli/04-check-run-commands.md](../cli/04-check-run-commands.md)** - Check/Run commands spec
- **[../../examples/README.md](../../examples/README.md)** - Examples guide

---

## References

- [CLI Implementation](../../src/compiler_bootstrap.gleam)
- [E2E Tests](../../test/core/examples_test.gleam)
- [Examples Directory](../../examples/core/)
