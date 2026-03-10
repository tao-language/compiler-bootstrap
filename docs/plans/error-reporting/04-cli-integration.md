# CLI Integration Plan

> **Goal**: Integrate rich error reporting into the CLI for both human and AI consumption
> **Status**: ⏳ In Progress - Infrastructure complete, implementing display
> **Date**: March 2025

---

## Overview

This document describes how to integrate the error reporting system into the CLI. The goals are:

1. **Human-readable output** - Beautiful terminal errors with source snippets
2. **Machine-readable output** - JSON for IDEs and AI (future)
3. **Consistent interface** - Same flags for all commands
4. **Exit codes** - Proper status codes for scripting (future)

---

## Implementation Status

### What's Ready

- ✅ Source snippet formatter (`syntax/source_snippet.gleam`)
- ✅ Error reporter module (`syntax/error_reporter.gleam`)
- ✅ Parse error to diagnostic conversion
- ✅ Error AST nodes for graceful recovery
- ✅ All 401 tests passing

### Implementation Plan

1. **Phase 1**: Basic error display with source snippets (parse errors)
2. **Phase 2**: Type error display with source snippets
3. **Phase 3**: Multi-span error support (type mismatches)
4. **Phase 4**: Error codes and suggestions
5. **Phase 5**: JSON output format
6. **Phase 6**: Exit codes

### Current Focus: Phase 1 ✅ COMPLETE

Display parse errors with source snippets in the CLI.

**Example Output:**
```
error[E0001]: Unexpected token
  ┌─ test_error.core.tao:1:1
1 │ {{{
    ^
2 │
  = note: Expected: valid alternative
  = note: Got: none
  = hint: Check syntax near this position
```

**Implementation:**
- ✅ Error reporter integration in `compiler_bootstrap.gleam`
- ✅ Source snippet display for parse errors
- ✅ Error codes (E0001 for parse errors)
- ✅ Notes and hints display
- ✅ All 401 tests passing

---

## Command-Line Interface

### Error Format Flag

```bash
gleam run check file.core.tao --error-format=human   # Default
gleam run check file.core.tao --error-format=json    # For IDEs/AI
gleam run check file.core.tao --error-format=short   # Just error type
```

### Color Flag

```bash
gleam run check file.core.tao --color=auto    # Default (detect TTY)
gleam run check file.core.tao --color=always  # Force color
gleam run check file.core.tao --color=never   # No color
```

### Quiet Flag

```bash
gleam run check file.core.tao --quiet   # Only errors, no "✓ Type checking"
```

---

## Human-Readable Output

### Success Case

```
$ gleam run check examples/01_identity.core.tao
✓ Type checking examples/01_identity.core.tao
✓ No errors found
```

### Single Error

```
$ gleam run check examples/bad_type.core.tao
error[E0101]: Type mismatch
   ┌─ examples/bad_type.core.tao:3:5
   │
 3 │ (x : $I32) -> x
   │     ^^^^^
   │
   = expected: $Type
   = got:      $I32
   │
   = note: Function parameter types must be $Type
   = hint: Try using $Type instead of $I32
   = help: https://errors.compiler-bootstrap.dev/E0101

✗ Type checking failed
```

### Multiple Errors

```
$ gleam run check examples/multiple_errors.core.tao
error[E0102]: Undefined variable
   ┌─ examples/multiple_errors.core.tao:1:8
   │
 1 │ x -> y
   │        ^
   │
   = 'y' is not defined
   = help: Did you mean 'x'?

error[E0101]: Type mismatch
   ┌─ examples/multiple_errors.core.tao:2:5
   │
 2 │ let z : $I32 = $Type
   │     ^^^^^^^^
   │
   = expected: $I32
   = got:      $Type
   │
   = note: Variable annotations must match inferred type

Found 2 errors
✗ Type checking failed
```

---

## JSON Output Format

### Schema

```typescript
interface Diagnostic {
  code: string;           // "E0101"
  severity: Severity;     // "error" | "warning" | "info"
  message: string;        // "Type mismatch"
  spans: Span[];          // Source locations
  children: Diagnostic[]; // Related diagnostics
  rendered: string;       // Human-readable output
}

interface Span {
  file_name: string;
  line_start: number;     // 1-based
  line_end: number;
  column_start: number;   // 1-based
  column_end: number;
  is_primary: boolean;
  label: string | null;
}
```

### Example Output

```json
{
  "diagnostics": [
    {
      "code": "E0101",
      "severity": "error",
      "message": "Type mismatch",
      "spans": [
        {
          "file_name": "examples/bad_type.core.tao",
          "line_start": 3,
          "line_end": 3,
          "column_start": 5,
          "column_end": 10,
          "is_primary": true,
          "label": "expected $Type"
        },
        {
          "file_name": "examples/bad_type.core.tao",
          "line_start": 3,
          "line_end": 3,
          "column_start": 14,
          "column_end": 15,
          "is_primary": false,
          "label": "got $I32"
        }
      ],
      "children": [
        {
          "message": "Function parameter types must be $Type",
          "spans": []
        }
      ],
      "rendered": "error[E0101]: Type mismatch\n   ┌─ examples/bad_type.core.tao:3:5\n   │\n 3 │ (x : $I32) -> x\n   │     ^^^^^\n   │\n   = expected: $Type\n   = got:      $I32\n"
    }
  ]
}
```

### Usage

```bash
# For IDE integration
gleam run check file.core.tao --error-format=json 2>&1 | \
  jq '.diagnostics[] | {code, message, file: .spans[0].file_name}'

# For AI analysis
gleam run check file.core.tao --error-format=json | \
  ai-fix --context src/
```

---

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success (no errors) |
| 1 | Parse errors |
| 2 | Type errors |
| 3 | Runtime errors |
| 4 | File not found |
| 5 | Invalid arguments |

### Implementation

```gleam
pub fn main() {
  let args = parse_args()
  
  case run_check(args) {
    Ok(0) -> io.exit(0)
    Ok(error_count) -> {
      io.println("\nFound " <> int.to_string(error_count) <> " error(s)")
      io.exit(2)  // Type errors
    }
    Error(ParseError) -> io.exit(1)
    Error(FileNotFound) -> io.exit(4)
    Error(InvalidArgs) -> io.exit(5)
  }
}
```

---

## Error Accumulation

Don't stop at the first error - show all errors:

```gleam
pub fn check_file(file: File) -> List(Error) {
  let parse_result = syntax.parse(file.contents)
  
  case parse_result.errors {
    [..] as errors -> errors  // Return all parse errors
    [] -> {
      let #(_ty, _ann, state) = core.infer(initial_state, parse_result.ast)
      state.errors  // Return all type errors
    }
  }
}
```

---

## Verbose Mode

```bash
$ gleam run check file.core.tao --verbose
✓ Loading file.core.tao
✓ Detected file type: Core language (.core.tao)
✓ Parsing...
✓ Parsed successfully (23 tokens)
✓ Type checking...
✓ Inferred type: (x : $Type) -> x
✓ Type checking file.core.tao
✓ No errors found
```

### Debug Mode

```bash
$ gleam run check file.core.tao --debug
AST:
NLam("x", NVar(0, span), span)

Type:
VPi("x", env, VTyp(0), VVar(0))
```

---

## Integration Points

### compiler_bootstrap.gleam

```gleam
fn check_core(file: File, verbose: Bool, debug: Bool, format: ErrorFormat) -> Result(Nil, Error) {
  let parse_result = syntax.parse(file.contents)
  
  case parse_result.errors {
    [..] as errors -> {
      let diagnostics = errors |> list.map(parse_error_to_diagnostic)
      output_diagnostics(diagnostics, format)
      Error(ParseError(diagnostics))
    }
    [] -> {
      let #(_ty, _ann, state) = infer(initial_state, parse_result.ast)
      
      case state.errors {
        [..] as errors -> {
          let diagnostics = errors |> list.map(type_error_to_diagnostic)
          output_diagnostics(diagnostics, format)
          Error(TypeError(diagnostics))
        }
        [] -> {
          io.println("✓ Type checking " <> file.path)
          io.println("✓ No errors found")
          Ok(Nil)
        }
      }
    }
  }
}
```

---

## AI Assistant Optimization

### Structured Hints

Include information useful for AI:

```gleam
pub type A IHint {
  A IHint(
    suggestion: String,     // Concrete fix
    confidence: Float,      // How confident (0.0-1.0)
    explanation: String,    // Why this fix
    alternative: List(String), // Other possible fixes
  )
}
```

### Example AI-Friendly Output

```json
{
  "code": "E0102",
  "message": "Undefined variable",
  "ai_hints": [
    {
      "suggestion": "Replace 'y' with 'x'",
      "confidence": 0.9,
      "explanation": "Variable 'x' is bound by the lambda at line 1",
      "alternatives": [
        "Add 'y' as a parameter: (y: $Type) -> y",
        "Define 'y' before use: let y = ..."
      ]
    }
  ]
}
```

---

## Testing

### Golden File Tests

```
-- tests/cli/check_success.txt --
$ gleam run check examples/01_identity.core.tao
✓ Type checking examples/01_identity.core.tao
✓ No errors found
$?
0
```

```
-- tests/cli/check_type_error.txt --
$ gleam run check examples/bad_type.core.tao
error[E0101]: Type mismatch
   ┌─ examples/bad_type.core.tao:3:5
   │
 3 │ (x : $I32) -> x
   │     ^^^^^
   │
   = expected: $Type
   = got:      $I32

✗ Type checking failed
$?
2
```

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Error reporting overview
- **[02-error-types.md](./02-error-types.md)** - Error type specifications
- **[03-source-snippets.md](./03-source-snippets.md)** - Source snippet formatting

---

## Implementation Checklist

- [ ] Add `--error-format` flag to CLI
- [ ] Add `--color` flag to CLI
- [ ] Implement JSON output format
- [ ] Implement proper exit codes
- [ ] Add error accumulation (don't stop at first error)
- [ ] Create `error_to_diagnostic()` functions
- [ ] Implement AI hints for common errors
- [ ] Add golden file tests for CLI output
- [ ] Test with real-world error scenarios
- [ ] Document error codes on website
