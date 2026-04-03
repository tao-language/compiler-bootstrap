# Compiler Bootstrap - Project Context

## Project Overview

A **Gleam project** providing a foundation for building compilers with:

1. **Dependently typed core language** - Bidirectional type checking, normalization by evaluation, exhaustiveness checking (Maraneng's algorithm)
2. **Language-agnostic parser combinator library** - Token-based parsing with Pratt parsing for operator precedence
3. **Language-agnostic formatter library** - Document algebra with automatic line breaking and configurable indentation
4. **Generic grammar DSL** - Single source of truth for generating parsers and formatters
5. **Tao language** - High-level functional language (TypeScript-like syntax) that desugars to core

## Building and Running

```bash
gleam run    # Run the project
gleam test   # Run tests
```

For continuous testing (requires `fswatch`):
```bash
fswatch -or src test | xargs -n1 -I{} gleam test
```

## Project Structure

```
src/
├── compiler_bootstrap.gleam  # CLI entry point
├── syntax/
│   ├── grammar.gleam         # Grammar DSL (~950 lines)
│   ├── lexer.gleam           # Tokenizer (~400 lines)
│   ├── formatter.gleam       # Document algebra (~440 lines)
│   ├── source_snippet.gleam  # Source snippet (~260 lines)
│   └── error_reporter.gleam  # Error reporting (~220 lines)
├── core/
│   ├── color.gleam           # ANSI color configuration
│   ├── core.gleam            # Core language (~3,400 lines)
│   ├── error_formatter.gleam # Error formatting with source snippets
│   └── syntax.gleam          # Core parser/formatter
├── tao/
│   ├── ast.gleam             # Tao AST (~430 lines)
│   ├── compiler.gleam        # Tao compiler
│   ├── desugar.gleam         # Desugaring to core
│   ├── global_context.gleam  # Module resolution
│   ├── import_ast.gleam      # Import AST
│   ├── import_resolver.gleam # Import resolution
│   ├── lexer.gleam           # Tao lexer
│   ├── syntax.gleam          # Tao syntax/parser
│   ├── test_filter.gleam     # Test filtering
│   ├── test_parser.gleam     # Test annotation parser
│   ├── test_reporter.gleam   # Test reporting
│   └── test_runner.gleam     # Test execution
└── examples/
    └── calc.gleam            # Calculator example with spans

test/
├── compiler_bootstrap_test.gleam
├── core/
│   ├── core_test.gleam
│   ├── error_formatter_test.gleam
│   ├── examples_test.gleam
│   ├── fix_test.gleam
│   └── pattern_match_test.gleam
├── syntax/
│   ├── grammar_test.gleam
│   ├── lexer_test.gleam
│   └── formatter_test.gleam
└── tao/
    ├── desugarer_test.gleam
    ├── examples_test.gleam
    ├── import_desugar_test.gleam
    ├── overloading_example_test.gleam
    ├── overloading_test.gleam
    ├── syntax_test.gleam
    ├── test_filter_test.gleam
    └── test_parser_test.gleam

docs/
├── README.md                 # Documentation index
├── cli.md                    # CLI usage guide
├── core.md                   # Core language specification
├── core-syntax.md            # Core syntax reference
├── lessons-learned.md        # Key insights from development
├── syntax-library.md         # Syntax library documentation
├── tao-syntax.md             # Tao syntax specification
└── plans/                    # Implementation plans
    ├── core/                 # Core language plans
    ├── syntax/               # Syntax library plans
    ├── tao/                  # Tao language plans
    ├── cli/                  # CLI plans
    ├── maintenance/          # Maintenance plans
    ├── error-reporting/      # Error reporting plans
    └── retrospective.md      # Comprehensive retrospective

examples/
└── tao/
    └── programs/
        ├── 01-basics/
        ├── 02-functions/
        ├── 03-pattern-matching/
        ├── 04-recursion/
        ├── 05-control-flow/
        ├── 06-modules/
        └── 07-advanced/
```

## Key Architecture Concepts

### Core Language (`src/core/core.gleam`)

- **Syntax (`Term`) vs Semantics (`Value`)**: Syntax uses De Bruijn **indices** (relative), values use De Bruijn **levels** (absolute)
- **Bidirectional type checking**: `infer` (synthesis) and `check` (verification) modes
- **Normalization by Evaluation**: Evaluate to value → quote back to syntax for equality
- **Error resilience**: Never stops on errors; accumulates all issues for IDE feedback
- **Exhaustiveness checking**: Integrated pattern match coverage via Maranget's matrix algorithm
- **Comptime evaluation**: Compile-time function execution with permission system
- **FFI support**: Built-in arithmetic, comparison, logical operations

### Syntax Library (`src/syntax/`)

- **Grammar DSL**: Declarative grammar definition with operator precedence
- **Lexer**: Token-based tokenizer with source location tracking
- **Formatter**: Document algebra with 16+ combinators, automatic line breaking
- **Error Reporter**: Source snippets with error highlights for diagnostics

### Tao Language (`src/tao/`)

- High-level functional language with TypeScript-like syntax
- Desugars to core language for type checking and evaluation
- Features: dependent types, result/maybe sugar, explicit mutability
- Includes test framework with annotations (`@skip`, `@timeout`, `@requires`)

## Current Status

### ✅ Complete and Working

| Component | Status | Tests |
|-----------|--------|-------|
| Syntax Library | Complete | 344 passing |
| Core Language | Complete | 263 passing |
| CLI | Complete | Working |
| Error Reporting | Complete | Working |
| Warning Cleanup | Complete | 45 → 0 warnings |
| **Total** | **All green** | **395 passing** |

### Key Features Working

- ✅ Recursive functions (`factorial(5) = 120`)
- ✅ Parser error recovery (graceful handling of missing values)
- ✅ Step counters prevent infinite loops (timeout protection)
- ✅ Exhaustiveness checking (conservative with guards)
- ✅ Test/Run statement support

## Development Conventions

### Code Style

- **Gleam style**: Functional, type-safe code with explicit error handling
- **Documentation**: Brief inline comments (`///`), detailed docs in `docs/`
- **Error handling**: Accumulate errors via `with_err`, return `VErr` to continue checking
- **Variable naming**: Prefix unused with `_`, but verify they're genuinely unused

### Testing

- **Framework**: `gleeunit` with `should` assertions
- **Structure**: Mirror `src/` in `test/` with `_test` suffix
- **Best practices**:
  - One assertion per test
  - Check structural equality, not just success
  - Test error cases, not just happy paths
  - Descriptive test names

### Important: Before Making "Cleanup" Changes

Read **[docs/lessons-learned.md](docs/lessons-learned.md)** first. Key insights:

1. **Correctness over cleanliness** - Don't blindly apply compiler warnings
2. **Some "dead code" is essential** - Spine structures, neutral terms are critical
3. **Type aliases can be semantic** - `Type = Value` documents type theory
4. **Test variables need context** - May be used in pattern matching
5. **Unreachable code after panic = bug** - Indicates contradictory logic
6. **Read the full warning message** - Gleam distinguishes "unused" from "passed but never used"
7. **Gleam has no `if`** - Uses `case` expressions exclusively

## Important: Read These First

| Document | Description |
|----------|-------------|
| **[docs/lessons-learned.md](docs/lessons-learned.md)** | Core principles from development |
| **[docs/plans/retrospective.md](docs/plans/retrospective.md)** | Comprehensive retrospective (1,800+ lines) |
| **[src/README.md](src/README.md)** | Code style guide |
| **[test/README.md](test/README.md)** | Testing guide |
| **[docs/core.md](docs/core.md)** | Core language specification |
| **[docs/cli.md](docs/cli.md)** | CLI usage guide |

## Key Commands

```bash
# Run the CLI
gleam run check path/to/file.core.tao
gleam run run path/to/file.core.tao
gleam run --help

# Run tests
gleam test

# Continuous testing
fswatch -or src test | xargs -n1 -I{} gleam test
```

## Dependencies

- `gleam_stdlib >= 0.44.0 and < 2.0.0`
- `argv >= 1.0.2 and < 2.0.0`
- `simplifile >= 2.4.0 and < 3.0.0`
- `gleeunit >= 1.0.0 and < 2.0.0` (dev)

## For AI Assistants

When working with this codebase:

1. **Always distinguish** `Term` (syntax) from `Value` (semantics)
2. **Remember** De Bruijn indices (relative) vs. levels (absolute)
3. **Error recovery** is intentional—don't "fix" `VErr` propagation
4. **Read full warning messages** before suggesting changes
5. **Check context** before marking variables as unused
6. **Quote should never evaluate** - This was a critical bug (now fixed)
7. **Read docs/lessons-learned.md** before making "cleanup" changes

## Recent Major Fixes (March 2026)

1. **Quote Re-evaluation Bug** - `quote` was calling `eval` for lambda bodies, causing exponential blowup. Fixed by using `quote_term_in_env` instead.

2. **Missing FFI in do_match** - `do_match` couldn't evaluate builtins in match bodies. Fixed by adding `ffi` parameter.

3. **Parser Semicolon Handling** - Program rule didn't consume semicolons between statements. Fixed by using `many(seq([Stmt, opt(Semi)]))`.

4. **Step Counter for Evaluation** - Added step limits to prevent infinite loops during evaluation and quoting.

## Test Results

- **395 tests passing** (100%)
- **0 failures**
- **0 warnings**

## Contact

- **GitHub**: Check repository for issues and discussions
- **Documentation**: See `docs/` directory for comprehensive guides
