# Compiler CLI Overview

> **Goal**: Command-line interface for checking and running core/tao files
> **Status**: ⏳ In Progress - Basic CLI works, output format needs updates
> **Date**: March 2025 (Updated March 2026)

---

## Core Insight

A unified CLI should handle both the core language and the high-level Tao language with the same commands, detecting the language from file extension.

```bash
gleam run check example.core.tao   # Type-check core file
gleam run run example.core.tao      # Evaluate core file
gleam run check example.tao         # Type-check tao file (future)
gleam run run example.tao           # Compile and run tao file (future)
```

---

## Architecture

### Module Structure

```
src/
├── compiler_bootstrap.gleam  # CLI entry point
├── syntax/
│   ├── grammar.gleam         # Grammar DSL and parser
│   ├── formatter.gleam       # Document algebra formatter
│   ├── lexer.gleam           # Tokenizer
│   ├── source_snippet.gleam  # Source snippet formatter
│   └── error_reporter.gleam  # Error to diagnostic conversion
├── core/
│   ├── syntax.gleam          # Core language parser/formatter
│   └── core.gleam            # Core evaluator and type checker
└── examples/                 # Example files and error cases
```

### Execution Pipeline

#### Core Files (`.core.tao`)

```
source → parse → Term → type_check → eval → Result
                   ↓              ↓
            error_reporter    format (for output)
```

#### Tao Files (`.tao`) - Future

```
source → parse → Tao AST → desugar → Term → type_check → Result
```

---

## Design Principles

1. **Unified interface** - Same commands for core and Tao
2. **File type detection** - Extension-based (`.core.tao` vs `.tao`)
3. **Error resilience** - Report all errors, not just the first
4. **Source locations** - Full span information in error messages
5. **Actionable errors** - Clear hints and suggestions for fixing errors
6. **Verbose output** - `--verbose` and `--debug` for debugging

---

## Implementation Status

### ✅ Complete and Working

**CLI Entry Point** (`src/compiler_bootstrap.gleam`):
- ✅ Command-line argument parsing with `argv` library
- ✅ Command types (`Check`, `Run`, `Help`)
- ✅ File type detection (`.core.tao` vs `.tao`)
- ✅ File I/O with `simplifile` library
- ✅ File not found error handling
- ✅ File read error handling
- ✅ Verbose mode (`-v`, `--verbose`)
- ✅ Debug mode (`--debug`) - prints AST
- ✅ Help command (`-h`, `--help`)
- ✅ Error reporting for unknown commands and invalid arguments

**Error Reporting**:
- ✅ Source snippet formatter (`syntax/source_snippet.gleam`)
- ✅ Error reporter module (`syntax/error_reporter.gleam`)
- ✅ Parse error to diagnostic conversion
- ✅ Type error to diagnostic conversion
- ✅ Multi-span error support (type mismatches)
- ✅ Error codes (E0001, E0101-E0106, E0201-E0202, E0301)
- ✅ Hints for all error types
- ✅ Source snippet display with line numbers and pointers

**Type Checking Integration**:
- ✅ `core.infer()` wired up in CLI
- ✅ Type errors formatted with source snippets
- ✅ All error types handled with diagnostics

**Commands**:
- ✅ `check <file>` - Type-check a file
- ✅ `run <file>` - Type-check and evaluate
- ✅ `--help` - Show help message
- ✅ `--verbose` - Verbose output
- ✅ `--debug` - Debug mode (print AST)

**Testing**:
- ✅ E2E tests with golden file comparison
- ✅ **424 tests passing**
- ✅ Auto-discovery of all examples

### ⏳ In Progress

**CLI Output Format**:
- [ ] `run` command should output result even on errors
- [ ] Error output to `stderr`, result to `stdout`
- [ ] Delimiter between errors and result
- [ ] Exit code handling (return 1 on errors even with result)
- [ ] Code snippets with 2-3 lines context (currently minimal)

**Error Message Quality**:
- [ ] Context lines (2-3 before/after error)
- [ ] "Did you mean?" suggestions
- [ ] Better type information in messages
- [ ] Error explanations (why, not just what)
- [ ] See **[../testing/05-error-message-improvements.md](../testing/05-error-message-improvements.md)**

### 📋 Planned

**Test Command**:
- [ ] `test <file|directory>` - Run example-based tests
- [ ] Recursive directory traversal
- [ ] Test result reporting with pass/fail
- [ ] Continue on check errors (like `run`)
- [ ] Exit code 1 on test failures
- [ ] See **[../tao/11-test-system.md](../tao/11-test-system.md)** for test system specification

**Tao Language Integration**:
- [ ] Wire up Tao parser (requires Tao lexer + grammar)
- [ ] Wire up Tao desugarer (requires Tao desugarer implementation)
- [ ] Tao-specific error messages
- [ ] See **[../tao/01-overview.md](../tao/01-overview.md)** for Tao implementation status

**CLI Enhancements**:
- [ ] Output file option (`--output`)
- [ ] Watch mode (`--watch`)
- [ ] Parallel type checking
- [ ] Performance profiling (`--profile`)

---

## Usage

### Basic Commands

```bash
# Type-check a file
gleam run check path/to/file.core.tao

# Type-check and evaluate a file
gleam run run path/to/file.core.tao

# Run example-based tests
gleam run test path/to/tests.tao
gleam run test path/to/tests/  # Test directory recursively

# Show help
gleam run --help
```

### Options

| Option | Short | Long | Description |
|--------|-------|------|-------------|
| Help | `-h` | `--help` | Show help message |
| Verbose | `-v` | `--verbose` | Verbose output |
| Debug | | `--debug` | Debug mode (print AST) |

### Examples

```bash
# Check a file for errors
gleam run check examples/hello.core.tao

# Run a file and print the result
gleam run run examples/add.core.tao

# Check with verbose output
gleam run check -v examples/hello.core.tao

# Run with debug output (print AST)
gleam run run --debug examples/hello.core.tao
```

---

## Error Reporting

The CLI provides detailed error messages with source snippets:

### Parse Errors

```
error[E0001]: Unexpected token
   ┌─ examples/error.core.tao:3:5
   │
 3 │ 1 + * 3
   │     ^
   │
   = Expected: expression
   = Got: *
   
Hint: Check syntax near this position
```

### Type Errors

```
error[E0101]: Type mismatch
   ┌─ examples/error.core.tao:5:10
   │
 5 │ (x : $I32) -> x
   │     ^^^^^
   │
   = expected: $Type
   = got:      $I32
   
Hint: Check that types are compatible
```

### Undefined Variables

```
error[E0102]: Undefined variable
   ┌─ examples/error.core.tao:3:5
   │
 3 │ x + 1
   │ ^
   │
Hint: Check variable name and scope
```

### Error Codes

| Code | Description |
|------|-------------|
| E0001 | Unexpected token (parse error) |
| E0101 | Type mismatch |
| E0102 | Undefined variable |
| E0103 | Not a function |
| E0104 | Arity mismatch |
| E0105 | Constructor undefined |
| E0106 | Unsolved hole |
| E0201 | Match missing case |
| E0202 | Match redundant case |
| E0301 | Comptime permission denied |

---

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success (no errors, all tests pass) |
| 1 | Type error, parse error, or test failure |
| 2 | Runtime error |
| 3 | File not found |
| 4 | Invalid arguments |

---

## Implementation Details

### Command Parsing

```gleam
pub fn main() {
  let args = command_line_args()
  
  case parse_args(args) {
    Ok(Check(file, verbose, debug)) -> run_check(file, verbose, debug)
    Ok(Run(file, verbose, debug)) -> run_run(file, verbose, debug)
    Ok(Help) -> print_help()
    Error(msg) -> {
      io.println("Error: " <> msg)
      io.exit(1)
    }
  }
}
```

### File Type Detection

```gleam
fn detect_file_type(path: String) -> FileType {
  case string.ends_with(path, ".core.tao") {
    True -> Core
    False -> {
      case string.ends_with(path, ".tao") {
        True -> Tao
        False -> Core  // Default to core
      }
    }
  }
}
```

### Error Reporting

```gleam
// Parse error
let diagnostic = error_reporter.parse_error_to_diagnostic(error, source, file)
source_snippet.format_diagnostic(diagnostic, source)

// Type error
let diagnostic = error_reporter.type_error_to_diagnostic(error, source, file)
source_snippet.format_diagnostic(diagnostic, source)
```

---

## Related Documents

- **[02-cli-parser.md](./02-cli-parser.md)** - CLI parser specification
- **[03-error-reporter.md](./03-error-reporter.md)** - Error reporter specification
- **[04-check-run-commands.md](./04-check-run-commands.md)** - Check/Run commands spec
- **[../../docs/cli.md](../../docs/cli.md)** - Complete CLI documentation
- **[../../docs/syntax-library.md](../../docs/syntax-library.md)** - Syntax library documentation
- **[../../docs/core.md](../../docs/core.md)** - Core language specification
- **[../syntax/01-overview.md](../syntax/01-overview.md)** - Syntax library overview
- **[../core/01-overview.md](../core/01-overview.md)** - Core language overview
- **[../tao/01-overview.md](../tao/01-overview.md)** - Tao language overview
- **[../tao/11-test-system.md](../tao/11-test-system.md)** - Test system specification
- **[../testing/01-overview.md](../testing/01-overview.md)** - Testing overview
- **[../testing/03-examples-testing.md](../testing/03-examples-testing.md)** - Examples testing spec
- **[../testing/05-error-message-improvements.md](../testing/05-error-message-improvements.md)** - Error improvements

---

## References

- [CLI Implementation](../../src/compiler_bootstrap.gleam)
- [Error Reporter](../../src/syntax/error_reporter.gleam)
- [Source Snippet](../../src/syntax/source_snippet.gleam)
- [Core Language](../../src/core/core.gleam)
- [Syntax Library](../../src/syntax/grammar.gleam)
