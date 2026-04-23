# CLI Check and Run Commands

> **Goal**: Implement `check` and `run` commands with proper error handling and output
> **Status**: ⏳ In Progress - Basic CLI exists, output format needs updates
> **Date**: March 11, 2026

---

## Overview

The CLI provides two main commands for processing source files:

| Command | Type Check | Evaluate | Output Errors | Output Result | Exit Code on Error |
|---------|------------|----------|---------------|---------------|-------------------|
| `check` | ✅ | ❌ | ✅ stderr | ❌ | 1 |
| `run` | ✅ | ✅ | ✅ stderr | ✅ stdout | 1 |

---

## Command Specifications

### `check` Command

**Purpose**: Type-check a file without evaluating.

**Pipeline**:
```
source → parse → Term → type_check → errors?
                              ↓
                        format_errors → stderr
```

**Exit Codes**:
- `0` - No errors
- `1` - Type errors or parse errors found

**Example**:
```bash
$ gleam run -- check examples/core/errors/type_errors/type_mismatch.core.tao
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
$ echo $?
1
```

### `run` Command

**Purpose**: Type-check and evaluate a file, showing result even if errors exist.

**Pipeline**:
```
source → parse → Term → type_check → eval → result
                              ↓          ↓
                        format_errors  format_result
                             ↓            ↓
                          stderr       stdout
```

**Exit Codes**:
- `0` - No errors
- `1` - Type errors or parse errors found (result still shown)

**Example**:
```bash
$ gleam run -- run examples/core/errors/type_errors/type_mismatch.core.tao
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
$ echo $?
1
```

---

## Output Format

### Error Output (stderr)

Errors are formatted using `error_formatter` with:
- Emoji-guided navigation (❌, 💡, 📝, 🔧)
- Source snippets with line numbers
- 2-3 lines of context before and after
- Inline error messages
- Notes and help suggestions

**Format**:
```
❌ error[E####]: Category
error[E####]: Message
   ┌─ file:line:col
   │
 N │ ... context before
 N │ source line with error
   │       ^^^^^ pointer
 N │ ... context after
   │
   💡 Hint 1
   💡 Hint 2
   📝 note: Additional context
   🔧 help: Suggestion
```

### Result Output (stdout)

The normalized term is output as a readable string:
- Literals: `42`, `3.14`
- Variables: `x`
- Lambdas: `x -> x`
- Applications: `f(x)`
- Constructors: `#Some(42)`
- Records: `{x: 1, y: 2}`

**Format**:
```
<normalized_term>
```

### Delimiter

When errors exist, a delimiter separates errors from result:
```
-----------------------------------------------------------
```

**ASCII art**: 59 dashes (`-`)

---

## Implementation

### Current State (`src/compiler_bootstrap.gleam`)

**What Works**:
- ✅ Command parsing (`check`, `run`, `help`)
- ✅ File type detection (`.core.tao`)
- ✅ File I/O
- ✅ Type checking integration
- ✅ Error reporting with source snippets
- ✅ Verbose and debug modes

**What Needs Updates**:
- [ ] `run` command should output result even on errors
- [ ] Error output to `stderr`, result to `stdout`
- [ ] Delimiter between errors and result
- [ ] Exit code handling
- [ ] Code snippets with 2-3 lines context

### Required Changes

#### 1. Separate stdout/stderr

```gleam
// Current: All output to stdout
io.println(output)

// Target: Errors to stderr, result to stdout
io.println(stderr, error_output)
io.println(stdout, result_output)
```

#### 2. Always show result in `run`

```gleam
// Current: Only show result if no errors
case state.errors {
  [] -> io.println(format_result(value))
  _ -> io.println(format_errors(state.errors))
}

// Target: Always show result
case state.errors {
  [] -> io.println(format_result(value))
  _ -> {
    io.println(stderr, format_errors(state.errors))
    io.println(stdout, delimiter)
    io.println(stdout, format_result(value))
  }
}
```

#### 3. Exit code handling

```gleam
// Current: Exit 1 on errors
case state.errors {
  [] -> io.exit(0)
  _ -> io.exit(1)
}

// Target: Same, but after showing result
case state.errors {
  [] -> io.exit(0)
  _ -> io.exit(1)  // Result already shown
}
```

#### 4. Code snippet context

Update `source_snippet.gleam` to show 2-3 lines before and after:

```gleam
// Current: Shows just the error line
// Target: Show context

let start_line = max(0, error_line - 2)
let end_line = min(total_lines, error_line + 3)
```

---

## Error Message Quality

### Current State

**What Works**:
- ✅ Error codes (E0001, E0101, etc.)
- ✅ Source snippets with line numbers
- ✅ Basic hints
- ✅ Emoji formatting

**Needs Improvement**:
- [ ] More specific error messages
- [ ] Better suggestions ("Did you mean?")
- [ ] Type information in messages
- [ ] Cross-reference related errors
- [ ] Explain _why_ something is wrong

### Improvement Plan

See **[05-error-message-improvements.md](./05-error-message-improvements.md)** for detailed improvement plan.

---

## Testing

### Golden File Testing

All CLI output is tested via golden files:

```bash
# Generate golden files
./scripts/generate_golden_files.sh

# Run tests
gleam test
```

### Test Coverage

- [ ] Success examples (programs, terms)
- [ ] Type error examples
- [ ] Syntax error examples
- [ ] Syntax recovery examples
- [ ] Exhaustiveness check examples
- [ ] Exit code verification

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Testing overview
- **[03-examples-testing.md](./03-examples-testing.md)** - Examples testing spec
- **[04-cli-golden-files.md](./04-cli-golden-files.md)** - Golden file format
- **[05-error-message-improvements.md](./05-error-message-improvements.md)** - Error improvements
- **[../cli/01-overview.md](../cli/01-overview.md)** - CLI overview

---

## References

- [CLI Implementation](../../src/compiler_bootstrap.gleam)
- [Error Formatter](../../src/core/error_formatter.gleam)
- [Source Snippet](../../src/syntax/source_snippet.gleam)
- [E2E Tests](../../test/core/examples_test.gleam)
