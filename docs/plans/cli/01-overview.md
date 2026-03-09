# Compiler CLI Overview

> **Goal**: Command-line interface for checking and running core/tao files
> **Status**: ✅ Complete - Full CLI with `argv` for args and `simplifile` for file I/O
> **Date**: March 2025

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
├── main.gleam              # CLI entry point
├── cli/
│   ├── parser.gleam        # Command-line argument parsing
│   ├── reporter.gleam      # Error/warning reporting
│   └── runner.gleam        # File loading and execution
├── core/
│   ├── syntax.gleam        # Core language parser/formatter
│   └── core.gleam          # Core evaluator and type checker
└── tao/                    # Tao language (future)
    ├── ast.gleam           # Tao AST
    ├── desugar.gleam       # Tao → Core desugaring
    └── ...
```

### Execution Pipeline

#### Core Files (`.core.tao`)

```
source → parse → Term → type_check → Result
                   ↓
               format (for error messages)
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
5. **Verbose output** - `--verbose` and `--debug` for debugging

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
- ✅ Parse error formatting with position info
- ✅ Verbose mode (`-v`, `--verbose`)
- ✅ Debug mode (`--debug`) - prints AST
- ✅ Help command (`-h`, `--help`)
- ✅ Error reporting for unknown commands and invalid arguments

**Commands**:
- ✅ `check <file>` - Type-check a file
- ✅ `run <file>` - Type-check and evaluate
- ✅ `--help` - Show help message
- ✅ `--verbose` - Verbose output
- ✅ `--debug` - Debug mode (print AST)

### ⏳ In Progress / Pending

**Type Checking Integration**:
- [ ] Wire up `core.infer()` in CLI
- [ ] Format and display type errors
- [ ] Add type error examples

**Exhaustiveness Checking**:
- [ ] Fix match expression parsing first
- [ ] Integrate exhaustiveness checker
- [ ] Add coverage error examples

**Error Message Improvements**:
- [ ] Source snippet formatting (like Rust)
- [ ] Line numbers and column pointers
- [ ] Context lines (before/after error)
- [ ] Helpful hints/suggestions

**Exit Codes**:
- [ ] Exit 0 on success
- [ ] Exit 1 on parse/type errors
- [ ] Exit 2 on runtime errors
- [ ] Exit 3 on file not found
- [ ] Exit 4 on invalid arguments

**Tao Language Support**:
- [ ] `.tao` file detection
- [ ] Tao parser integration
- [ ] Tao desugaring integration
- [ ] Tao type checking integration

**Enhanced Error Reporting**:
- [ ] Source snippet formatting (like Rust compiler)
- [ ] Multi-line error contexts
- [ ] Hint suggestions
- [ ] Warning support (currently only errors)

**Additional Features**:
- [ ] `--output` flag for compiled output
- [ ] `--watch` mode for development
- [ ] Exit code 2 (runtime error) implementation
- [ ] Exit code 3 (file not found) implementation
- [ ] Exit code 4 (invalid arguments) implementation

**Documentation**:
- [ ] User-facing CLI documentation
- [ ] Examples in repository
- [ ] README with usage instructions

---

## Current Usage

```bash
# Show help
gleam run -- --help

# Check a file
gleam run -- check path/to/file.core.tao

# Run a file
gleam run -- run path/to/file.core.tao

# With verbose output
gleam run -- run path/to/file.core.tao --verbose

# With debug output (prints AST)
gleam run -- run path/to/file.core.tao --debug
```

---

## Supported Commands

### `check` - Type Checking

Type-checks a file without running it. Reports all errors with source locations.

```bash
gleam run check example.core.tao
```

**Success Output:**
```
✓ Type checking example.core.tao
✓ No errors found
```

**Error Output:**
```
✗ Type checking example.core.tao
Error: Type mismatch
  ┌─ example.core.tao:5:10
  │
5 │ let x = (x : $I32)
  │          ^^^^^^^^^ Expected $Type, got $I32
```

### `run` - Evaluate

Type-checks and evaluates a file, printing the result.

```bash
gleam run run example.core.tao
```

**Output:**
```
✓ Type checking example.core.tao
✓ Evaluating...
Result: 42
```

---

## File Type Detection

File type is determined by extension:

| Extension | Language | Status |
|-----------|----------|--------|
| `.core.tao` | Core language | ✅ Implemented |
| `.tao` | Tao high-level language | 📋 Future |

### Core Language (`.core.tao`)

Direct parsing and type-checking using `core/syntax` and `core/core`.

### Tao Language (`.tao`) - Future

Parse Tao AST, desugar to core, then type-check.

---

## Command-Line Interface

### Usage

```
compiler-bootstrap <command> <file>

Commands:
  check <file>    Type-check a file
  run <file>      Type-check and evaluate a file

Options:
  -h, --help      Show help
  -v, --verbose   Verbose output
  --debug         Debug mode (print AST)

Examples:
  gleam run check example.core.tao
  gleam run run example.core.tao
  gleam run check --verbose example.core.tao
```

### Argument Parsing

```gleam
pub type Command {
  Check(file: String, verbose: Bool, debug: Bool)
  Run(file: String, verbose: Bool, debug: Bool)
  Help
}

pub fn parse_args(args: List(String)) -> Result(Command, String) {
  // Parse command-line arguments
  // Returns Command or error message
}
```

---

## Error Reporter

Formats errors with source locations and context.

```gleam
pub type Severity {
  Error
  Warning
  Info
}

pub type Diagnostic {
  Diagnostic(
    severity: Severity,
    message: String,
    span: Span,
    hint: Option(String),
  )
}

pub fn report(diagnostic: Diagnostic) -> formatter.Doc {
  // Format diagnostic with source snippet
  // Similar to Rust compiler errors
}
```

**Example Output:**
```
error: Type mismatch
  ┌─ example.core.tao:5:10
  │
5 │ let x = (x : $I32)
  │          ^^^^^^^^^ Expected $Type, got $I32
  │
  = hint: Try using $Type instead
```

---

## Verbose Mode

When `--verbose` is passed:

```
✓ Loading example.core.tao
✓ Parsing...
  AST: Term(Lam("x", Var(0)), ...)
✓ Type checking...
  Inferred type: (x : $Type) -> $Type
✓ No errors found
```

---

## Debug Mode

When `--debug` is passed:

```
✓ Parsing...
AST:
Term(
  data: Lam(
    name: "x",
    body: Term(
      data: Var(0),
      span: Span(...)
    )
  ),
  span: Span(...)
)

✓ Type checking...
Type: Pi("x", Typ(0), Typ(0))

✓ Evaluation...
Value: VLam("x", Closure(...))
```

---

## Example Sessions

### Successful Check

```bash
$ gleam run check examples/hello.core.tao
✓ Type checking examples/hello.core.tao
✓ No errors found
```

### Type Error

```bash
$ gleam run check examples/bad.core.tao
✗ Type checking examples/bad.core.tao
Error: Type mismatch
  ┌─ examples/bad.core.tao:3:5
  │
3 │ (x : $I32) -> x
  │     ^^^^^ Expected $Type, got $I32
```

### Successful Run

```bash
$ gleam run run examples/add.core.tao
✓ Type checking examples/add.core.tao
✓ Evaluating...
Result: 42
```

### Runtime Error

```bash
$ gleam run run examples/div_zero.core.tao
✓ Type checking examples/div_zero.core.tao
✓ Evaluating...
✗ Runtime error: Division by zero
```

### File Not Found

```bash
$ gleam run check nonexistent.core.tao
✗ File not found: nonexistent.core.tao
```

### Help

```bash
$ gleam run --help
compiler-bootstrap - Core language compiler

Usage: gleam run <command> <file>

Commands:
  check <file>    Type-check a file
  run <file>      Type-check and evaluate a file

Options:
  -h, --help      Show this help message
  -v, --verbose   Verbose output
  --debug         Debug mode (print AST and types)

Examples:
  gleam run check example.core.tao
  gleam run run example.core.tao
  gleam run check --verbose example.core.tao
```

---

## Related Documents

- **[02-cli-parser.md](./02-cli-parser.md)** - Command-line argument parsing specification
- **[03-error-reporter.md](./03-error-reporter.md)** - Error reporting and formatting
- **[../core/01-overview.md](../core/01-overview.md)** - Core language overview
- **[../core/06-production-ready.md](../core/06-production-ready.md)** - Production ready plan
- **[../core/07-fix-match-parsing.md](../core/07-fix-match-parsing.md)** - Fix match parsing
- **[../core/08-type-checker-integration.md](../core/08-type-checker-integration.md)** - Type checker integration

---

## References

- [CLI Implementation](../../src/compiler_bootstrap.gleam)
- [Core Language](../../src/core/core.gleam)
- [Syntax Library](../../src/syntax/grammar.gleam)
- [argv Library](https://hexdocs.pm/argv/)
- [simplifile Library](https://hexdocs.pm/simplifile/)
