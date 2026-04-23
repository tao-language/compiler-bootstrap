# Type Checker Integration Plan

> **Goal**: Integrate core type checker with CLI for proper type checking
> **Status**: 📋 Planned
> **Priority**: Critical (Phase 1)
> **Date**: March 2025

---

## Problem Statement

The CLI currently only performs parsing, not type checking. This means:
- Type errors are not detected
- Invalid programs pass the `check` command
- Type information is not displayed in verbose mode

---

## Current Implementation

### CLI Check Flow (from `src/compiler_bootstrap.gleam`)

```gleam
fn check_core(file: File, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  case verbose {
    True -> io.println("✓ Parsing...")
    False -> Nil
  }

  let parse_result = syntax.parse(file.contents)

  case parse_result.errors {
    [err, ..] -> {
      io.println("✗ Parse error:")
      io.println(format_parse_error(err))
      Error(ParseError(parse_result.errors |> list.map(format_parse_error)))
    }
    [] -> {
      // TODO: Add type checking here
      io.println("✓ Type checking " <> file.path)
      io.println("✓ No errors found")
      Ok(Nil)
    }
  }
}
```

### Type Checker API (from `src/core/core.gleam`)

```gleam
pub type State {
  State(
    // Type checking state
  )
}

pub type InferResult {
  InferResult(term: Term, typ: Term, state: State)
}

pub fn infer(state: State, term: Term) -> Result(InferResult, TypeError) {
  // Bidirectional type inference
}

pub fn check(state: State, term: Term, expected: Term) -> Result(Term, TypeError) {
  // Type checking against expected type
}
```

### Type Error Type

```gleam
pub type TypeError {
  TypeMismatch(expected: Term, actual: Term, span: Span)
  OccursCheck(variable: String, span: Span)
  UnboundVariable(name: String, span: Span)
  // ... other variants
}
```

---

## Integration Plan

### Step 1: Import Core Module

**File**: `src/compiler_bootstrap.gleam`

**Add Import**:
```gleam
import core/core.{
  type InferResult,
  type TypeError,
  infer,
  check,
  state_new,  // or however state is initialized
}
```

### Step 2: Add Type Error to CLI Error Type

**File**: `src/compiler_bootstrap.gleam`

**Add**:
```gleam
pub type Error {
  // ... existing variants
  CoreTypeError(message: String, span: Option(Span))
}
```

### Step 3: Implement Type Checking in `check_core`

**File**: `src/compiler_bootstrap.gleam`

**Update**:
```gleam
fn check_core(file: File, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  case verbose {
    True -> io.println("✓ Parsing...")
    False -> Nil
  }

  let parse_result = syntax.parse(file.contents)

  case parse_result.errors {
    [err, ..] -> {
      io.println("✗ Parse error:")
      io.println(format_parse_error(err))
      Error(ParseError(parse_result.errors |> list.map(format_parse_error)))
    }
    [] -> {
      case verbose {
        True -> {
          io.println("✓ Parsed successfully")
          io.println("✓ Type checking...")
        }
        False -> Nil
      }

      // Type check the parsed term
      let initial_state = core.state_new()
      case core.infer(initial_state, parse_result.ast) {
        Ok(infer_result) -> {
          case verbose {
            True -> {
              io.println("✓ Type checking " <> file.path)
              io.println("✓ Inferred type: " <> format_term(infer_result.typ))
              io.println("✓ No errors found")
            }
            False -> {
              io.println("✓ Type checking " <> file.path)
              io.println("✓ No errors found")
            }
          }
          Ok(Nil)
        }
        Error(type_err) -> {
          io.println("✗ Type error:")
          io.println(format_type_error(type_err))
          Error(CoreTypeError(format_type_error(type_err), get_span_from_error(type_err)))
        }
      }
    }
  }
}
```

### Step 4: Implement Type Error Formatting

**File**: `src/compiler_bootstrap.gleam`

**Add**:
```gleam
fn format_type_error(err: TypeError) -> String {
  case err {
    TypeError.TypeMismatch(expected, actual, span) -> {
      let expected_str = syntax.format(expected)
      let actual_str = syntax.format(actual)
      "Type mismatch at " <> format_span(span) <> "\n"
      <> "  Expected: " <> expected_str <> "\n"
      <> "  Actual: " <> actual_str
    }
    TypeError.OccursCheck(variable, span) -> {
      "Occurs check failed for variable '" <> variable <> "' at " <> format_span(span) <> "\n"
      <> "  This would create a recursive type"
    }
    TypeError.UnboundVariable(name, span) -> {
      "Unbound variable '" <> name <> "' at " <> format_span(span)
    }
    // ... handle other variants
  }
}

fn format_span(span: syntax.Span) -> String {
  // Format span as "line:column"
  // TODO: Implement proper span formatting
  "line " <> int.to_string(span.start_line)
  <> ", column " <> int.to_string(span.start_col)
}

fn get_span_from_error(err: TypeError) -> Option(syntax.Span) {
  case err {
    TypeError.TypeMismatch(_, _, span) -> Some(span)
    TypeError.OccursCheck(_, span) -> Some(span)
    TypeError.UnboundVariable(_, span) -> Some(span)
    // ... other variants
  }
}
```

### Step 5: Update Run Command

**File**: `src/compiler_bootstrap.gleam`

**Update** `run_core` to also type check before evaluation:

```gleam
fn run_core(file: File, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  // First type check
  let check_result = check_core(file, verbose, debug)
  case check_result {
    Error(err) -> Error(err)
    Ok(_) -> {
      // Then evaluate
      case verbose {
        True -> io.println("✓ Evaluating...")
        False -> Nil
      }

      // TODO: Add evaluation
      let formatted = syntax.format(parse_result.ast)
      io.println("Result: " <> formatted)
      Ok(Nil)
    }
  }
}
```

Wait, that's not quite right. Let me refactor to avoid duplicating the parse logic...

Better approach:

```gleam
fn run_core(file: File, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  case verbose {
    True -> io.println("✓ Parsing...")
    False -> Nil
  }

  let parse_result = syntax.parse(file.contents)

  case parse_result.errors {
    [err, ..] -> {
      io.println("✗ Parse error:")
      io.println(format_parse_error(err))
      Error(ParseError(parse_result.errors |> list.map(format_parse_error)))
    }
    [] -> {
      case verbose {
        True -> {
          io.println("✓ Parsed successfully")
          io.println("✓ Type checking...")
        }
        False -> Nil
      }

      // Type check
      let initial_state = core.state_new()
      case core.infer(initial_state, parse_result.ast) {
        Ok(infer_result) -> {
          case verbose {
            True -> {
              io.println("✓ Type checking " <> file.path)
              io.println("✓ Evaluating...")
            }
            False -> {
              io.println("✓ Type checking " <> file.path)
              io.println("✓ Evaluating...")
            }
          }

          // Evaluate
          let value = core.eval(infer_result.state, infer_result.term)
          let value_str = format_value(value)
          io.println("Result: " <> value_str)
          Ok(Nil)
        }
        Error(type_err) -> {
          io.println("✗ Type error:")
          io.println(format_type_error(type_err))
          Error(CoreTypeError(format_type_error(type_err), get_span_from_error(type_err)))
        }
      }
    }
  }
}
```

### Step 6: Add Type Error Examples

**Directory**: `examples/core/errors/type_errors/`

**Create Examples**:

```gleam
// 01_type_mismatch.core.tao
// Type mismatch: annotating term with wrong type
(x : $I32)
```

```gleam
// 02_occurs_check.core.tao
// Occurs check: recursive type
// This should fail because x would need to contain itself
(x : x -> x) -> x
```

```gleam
// 03_unbound_variable.core.tao
// Unbound variable: using undefined variable
undefined_var
```

---

## Testing Plan

### Test 1: Well-Typed Program

```gleam
// Should pass type checking
x -> x
```

**Expected**: "✓ No errors found"

### Test 2: Type Mismatch

```gleam
// Should fail type checking
(x : $I32)
```

**Expected**: "✗ Type error: Type mismatch"

### Test 3: Occurs Check

```gleam
// Should fail occurs check
(x : x -> x) -> x
```

**Expected**: "✗ Type error: Occurs check failed"

### Test 4: Unbound Variable

```gleam
// Should fail with unbound variable
undefined_var
```

**Expected**: "✗ Type error: Unbound variable"

### Test 5: Verbose Mode

```bash
gleam run -- check examples/core/01_identity.core.tao --verbose
```

**Expected Output**:
```
✓ Parsing...
✓ Parsed successfully
✓ Type checking...
✓ Type checking examples/core/01_identity.core.tao
✓ Inferred type: (x : $Type) -> $Type
✓ No errors found
```

---

## Files to Modify

| File | Changes |
|------|---------|
| `src/compiler_bootstrap.gleam` | Add type checking integration, error formatting |
| `examples/core/errors/type_errors/` | Add type error examples |
| `examples/core/errors/type_errors/README.md` | Update with working examples |

---

## Dependencies

Before this can be implemented:
- [ ] Fix match expression parsing (some programs may use match)
- [ ] Verify `core.infer()` API is stable
- [ ] Verify `core.state_new()` or equivalent exists

---

## Acceptance Criteria

- [ ] Well-typed programs pass `check` command
- [ ] Type errors are detected and reported
- [ ] Error messages include source locations
- [ ] Verbose mode shows inferred types
- [ ] `run` command type checks before evaluation
- [ ] Type error examples demonstrate common errors

---

## Estimated Effort

**Time**: 4-6 hours

**Complexity**: Medium

**Risk**: Medium (depends on core API stability)

---

## Related Documents

- **[06-production-ready.md](./06-production-ready.md)** - Production ready plan
- **[07-fix-match-parsing.md](./07-fix-match-parsing.md)** - Fix match parsing
- **[../cli/01-overview.md](../cli/01-overview.md)** - CLI documentation

---

## References

- [Core Type Checker](../../src/core/core.gleam)
- [CLI Implementation](../../src/compiler_bootstrap.gleam)
- [Type Error Examples](../../examples/core/errors/type_errors/)
