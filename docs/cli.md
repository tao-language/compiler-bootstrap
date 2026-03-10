# Compiler CLI Documentation

> **Version**: 1.0.0
> **Description**: Command-line interface for checking and running core/tao files

---

## Overview

The Compiler Bootstrap CLI provides a unified interface for checking and running both the core language and the high-level Tao language.

### Key Features

- **Unified interface** - Same commands for core and Tao
- **File type detection** - Extension-based (`.core.tao` vs `.tao`)
- **Error resilience** - Report all errors, not just the first
- **Source locations** - Full span information in error messages
- **Actionable errors** - Clear hints and suggestions for fixing errors
- **Verbose output** - `--verbose` and `--debug` for debugging

---

## Installation

```bash
# Clone the repository
git clone https://github.com/your-org/compiler-bootstrap.git
cd compiler-bootstrap

# Build and run
gleam run -- <command> [options]
```

---

## Usage

### Basic Commands

```bash
# Type-check a file
gleam run check path/to/file.core.tao

# Type-check and evaluate a file
gleam run run path/to/file.core.tao

# Show help
gleam run --help
gleam run check --help
gleam run run --help
```

### Options

| Option | Short | Long | Description |
|--------|-------|------|-------------|
| Help | `-h` | `--help` | Show help message |
| Verbose | `-v` | `--verbose` | Verbose output (show parsing, type checking steps) |
| Debug | | `--debug` | Debug mode (print AST and types) |

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

## File Types

### Core Language (`.core.tao`)

Core language files use the core syntax directly:

```tao
// examples/hello.core.tao
λx. x
```

```bash
gleam run check examples/hello.core.tao
gleam run run examples/hello.core.tao
```

### Tao Language (`.tao`) - Future

Tao language files use the high-level Tao syntax:

```tao
// examples/hello.tao
fn identity<a>(x: a) -> a {
  x
}
```

```bash
gleam run check examples/hello.tao
gleam run run examples/hello.tao
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

## Implementation Details

### Command Parsing

The CLI uses the `argv` library for command-line argument parsing:

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

File type is detected by extension:

```gleam
fn detect_file_type(path: String) -> FileType {
  case string.ends_with(path, ".core.tao") {
    True -> Core
    False -> {
      case string.ends_with(path, ".tao") {
        True -> Tao
        False -> Core  // Default to core for unknown extensions
      }
    }
  }
}
```

### Error Reporting

Errors are converted to diagnostics with source snippets:

```gleam
// Parse error
let diagnostic = error_reporter.parse_error_to_diagnostic(error, source, file)
source_snippet.format_diagnostic(diagnostic, source)

// Type error
let diagnostic = error_reporter.type_error_to_diagnostic(error, source, file)
source_snippet.format_diagnostic(diagnostic, source)
```

---

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success |
| 1 | Type error or parse error found |
| 2 | Runtime error |
| 3 | File not found |
| 4 | Invalid arguments |

---

## Troubleshooting

### File Not Found

```
error: File not found: path/to/file.core.tao
```

**Solution**: Check that the file path is correct and the file exists.

### Permission Denied

```
error: File read error:
  Path: path/to/file.core.tao
  Error: Permission denied
```

**Solution**: Check file permissions and ensure you have read access.

### Syntax Error

```
error[E0001]: Unexpected token
   ┌─ file.core.tao:3:5
   │
 3 │ 1 + * 3
   │     ^
```

**Solution**: Check the syntax near the indicated position. Common issues:
- Missing operand
- Extra operator
- Mismatched parentheses

### Type Error

```
error[E0101]: Type mismatch
   ┌─ file.core.tao:5:10
   │
 5 │ (x : $I32) -> x
   │     ^^^^^
```

**Solution**: Check that types are compatible. Common issues:
- Using a type where a term is expected
- Mismatched function argument types
- Incorrect type annotation

---

## Examples

### Hello World

```tao
// examples/hello.core.tao
λx. x
```

```bash
$ gleam run run examples/hello.core.tao
✓ Type checking examples/hello.core.tao
✓ Evaluating...
Result: λx. x
```

### Addition

```tao
// examples/add.core.tao
(λf. λx. f (f x)) (λn. λf. λx. n f (f x))
```

```bash
$ gleam run run examples/add.core.tao
✓ Type checking examples/add.core.tao
✓ Evaluating...
Result: λf. λx. f (f (f (f x)))
```

### Type Error

```tao
// examples/type_error.core.tao
(x : $I32) -> x
```

```bash
$ gleam run check examples/type_error.core.tao
✗ Type checking examples/type_error.core.tao
error[E0101]: Type mismatch
   ┌─ examples/type_error.core.tao:1:5
   │
 1 │ (x : $I32) -> x
   │     ^^^^^
   │
   = expected: $Type
   = got:      $I32
```

---

## Related Documents

- **[plans/cli/01-overview.md](plans/cli/01-overview.md)** - CLI overview and status
- **[plans/cli/02-cli-parser.md](plans/cli/02-cli-parser.md)** - CLI parser specification
- **[plans/cli/03-error-reporter.md](plans/cli/03-error-reporter.md)** - Error reporter specification
- **[syntax-library.md](syntax-library.md)** - Syntax library documentation
- **[core.md](core.md)** - Core language specification

---

## References

- [CLI Implementation](src/compiler_bootstrap.gleam)
- [Error Reporter](src/syntax/error_reporter.gleam)
- [Source Snippet](src/syntax/source_snippet.gleam)
- [Core Language](src/core/core.gleam)
- [Syntax Library](src/syntax/grammar.gleam)
