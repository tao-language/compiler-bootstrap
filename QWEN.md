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
│   ├── test_parser.gleam     # Test annotation parsing
│   ├── test_reporter.gleam   # Test reporting
│   └── test_api.gleam        # Test execution (parses, compiles, type-checks, runs tests)
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
├── tao/
│   ├── desugarer_test.gleam
│   ├── examples_test.gleam
│   ├── import_desugar_test.gleam
│   ├── overloading_example_test.gleam
│   ├── overloading_test.gleam
│   ├── syntax_test.gleam
│   ├── test_filter_test.gleam
│   ├── test_parser_test.gleam
│   └── test_api_unit_test.gleam  # Unit tests for test_api module
├── lib/
│   └── prelude/
│       └── bool_test.gleam   # Prelude module tests

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
| **Total** | **All green** | **470 passing** |

### Key Features Working

- ✅ Recursive functions (`factorial(5) = 120`)
- ✅ Parser error recovery (graceful handling of missing values)
- ✅ Step counters prevent infinite loops (timeout protection)
- ✅ Exhaustiveness checking (conservative with guards)
- ✅ Test/Run statement support
- ✅ Match expressions with different result types across functions

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

- **470 tests passing**
- **0 failures**
- **0 warnings**

### Recent Fixes (April 2026)

1. **Match Expression Type Inference** — Fixed match expressions working correctly with different result types across functions. Previously caused `InfiniteType` errors due to hole ID management in match motives. Fixed by:
   - Simplifying desugarer to always use `Hole(-1)` for unknown types (removed complex hole counter)
   - `infer` now instantiates ALL negative holes to fresh positive holes via `new_hole()`
   - Removed redundant `solve_motive_hole` — unification handles hole solving naturally
   - Combined with existing return type parsing fix (`find_arrow_type_expr` + `expr_to_type_string`), all match-related failures are resolved
   - Added 5 regression tests in `test/core/match_regression_test.gleam`

2. **Prelude Bool Test Count** — Fixed `lib_prelude_bool_module_test` to expect 18 test results (matching actual count of `~>` expressions in `lib/prelude/bool.tao`), was incorrectly expecting 20.

3. **InfiniteType Bug Fix** - Fixed `exprs_to_stmts` to handle `SimpleFn` expressions, converting them to `StmtFn` with return type annotations preserved. This prevented `collect_annotated_types` from collecting function types, causing module-level lambdas to use holes for parameter types.

4. **Two-Pass Module Type Collection** - Added `collect_annotated_types` function to collect function type annotations before desugaring, then use them for module-level lambda parameter types.

5. **Test Expression Constructor Environment** - Added `desugar_module_with_ctrs` to pass the main module's constructor environment to test expression evaluation, preventing `CtrUndefined` errors in test expressions.

6. **TypeDecl Grammar Rule Fix** - Fixed the `TypeDecl` grammar rule in `src/tao/syntax.gleam` (line ~994) which was falling through to an empty fallback because:
   - `seq` **flattens** sub-patterns — the inner `seq([Ident, opt(...)])` for the first constructor produces `TokenValue` directly in the flat list, not wrapped in `ListValue`
   - `many` wraps EACH iteration in a `ListValue`, and these are **siblings** in the flat list (not nested)
   - The fix extracts the type name at position 1, first constructor name at position 3, then scans the flat list for `ListValue` items (from `many`) to extract additional constructor names

7. **Unification Performance Fix** - The `occurs` check in `src/core/unify.gleam` was traversing entire environments for `VPi`/`VFix`/`VLam` values, causing exponential blowup during type-checking of modules with multiple functions (52s for bool.tao). Fixed by only checking explicit type components (domain for VPi, term for codomain) instead of the entire captured environment. This reduced bool.tao type-checking from 52s to 2s.

8. **Dynamic Prelude Loading** - Removed ALL hardcoded prelude knowledge from the compiler:
   - Added `ctr_env` field to `ModuleRef` to store constructor definitions per module
   - `with_prelude()` now parses prelude source files from `lib/prelude/*.tao`
   - Imports merge the imported module's `ctr_env` into `dc.ctrs`
   - All modules create records with holes for public names
   - Types resolved through `dc.ctrs` during type-checking

16. **Match Case Body Environment** — `desugar_single_case` called `core_term_to_term(core_body)` with empty env `[]`, causing all `CoreVar(name)` in case bodies to default to `Var(0)`. At type-checking, `Var(0)` resolved to the match motive's `"_"` parameter (typed as a fresh hole), making both function and argument have the same hole type → `InfiniteType`. **Fix**: Keep case bodies as `CoreTerm` (not converted), then convert in `core_term_to_term_loop` with the correct environment containing enclosing lambda/let/fix bindings.

17. **CLI Test Command Error Reporting** — The CLI `gleam run test` command used `test_runner.gleam` which had a stub `desugar_expression()` that always returned `CoreErr`, causing all tests to false-positive pass (both sides evaluated to `VErr`). Prelude file errors were silently ignored because files were never compiled/type-checked. **Fix**: Migrated CLI to use `test_api.run_test_file()` which properly parses, compiles, type-checks, and runs tests. Deleted `test_runner.gleam`. Added unit tests for error reporting.

18. **Boolean Operators as FFI Builtins** — `not(x)`, `and(x, y)`, `or(x, y)` were being parsed as unary/binary operators (`UnaryOp`, `BinOp`) and desugared to `CoreCall` (FFI builtin calls), producing `%call not(#True)` instead of calling user-defined functions. **Fix**: Changed `desugar_unaryop` and `desugar_binop` to create `CoreApp(CoreVar(name), ...)` for `not`/`and`/`or` instead of `CoreCall`, so they resolve to user-defined functions. Also fixed `VFix` evaluation to unwrap `Ann`-wrapped lambdas for annotated functions. Fixed incorrect test expectations for `implies(False, True)` and `implies(False, False)`.

19. **Generic Error Messages in Test Runner** — Test failures showed generic placeholders like `<parse error>` and `<type error>` instead of actual error details. **Fix**: Added `format_parse_errors`, `format_type_errors`, and `format_core_error` helper functions to `test_api.gleam`. All 4 error placeholders now show specific messages:
    - Parse errors: `"Parse error: expected X, got Y"`
    - Type errors: `"Syntax error: expected X, got Y"`, `"Type error: type mismatch"`, `"Constructor error: undefined constructor 'A'"`, etc.
    - Type mismatches: `"Type mismatch: expected %I32, got #Bool"`

20. **Non-Zero Exit Code on Test Failure** — The CLI `gleam run test` always exited with code 0 even when tests failed. **Fix**: Added `src/exit_code.gleam` with `erlang:halt/1` external function. `run_test_command` now returns `Bool` and `main` calls `exit_code.exit(1)` on failure.

21. **Test Failure Location** — Test failures showed `✗ FAIL: test expression` without file/line context. **Fix**: Added `file: String, line: Int` fields to `TestResult.Pass` and `TestResult.Fail`. Output now shows `✗ FAIL: path/to/file.tao:15: test expression` for quick navigation to the failing test.

22. **Infix Boolean Operators Not Parsed** — Python-style `x and y` and `x or y` syntax was not recognized as infix operators. The grammar's `operators` table defined them (lines 689-690) but the `left_assoc_rule("Logic", ...)` only included `&&` and `||`, not `and` and `or`. This caused `False and True` to be parsed incorrectly (only `False` was parsed, `and True` was left unparsed). **Fix**: Added `infix_binary("and", ...)` and `infix_binary("or", ...)` to the Logic level's `left_assoc_rule` in `src/tao/syntax.gleam`. Updated `lib/prelude/bool.tao` test expressions to use Python-style syntax: `not x`, `x and y`, `x or y`. Added 4 new unit tests for infix operators.

23. **Import Resolution for Python-Style Operators** — Imported prelude functions (`import prelude/bool {and, or, not}`) with Python-style operators (`True and True`) failed with "Type error: type mismatch". **Root cause**: When `get_module_function_bodies` extracted function bodies from the prelude source, it used the importing file's DesugarContext which had an empty `ctrs` (constructor environment). When desugaring function bodies containing constructors like `True` and `False`, `lookup_type_in_ctrs(dc.ctrs, "True")` returned false, causing constructors to become `CoreHole` instead of `CoreCtr("True", [])`. **Fix**: Added `process_imported_module_types` helper that processes type definitions from the imported module's body to populate `dc.ctrs` before extracting function bodies. Updated `lib/prelude/bool.test.tao` to use Python-style syntax. Added 6 new unit tests for import resolution with Python-style operators.

### Known Issues

**None** — All 470 tests pass with 0 failures and 0 warnings.

### Test System Architecture

| System | Entry Point | Status |
|--------|------------|--------|
| **Gleam tests** (`gleam test`) | `test/lib/prelude/bool_test.gleam` | ✅ Uses `test_api.run_test_file()` — catches errors |
| **CLI test** (`gleam run test`) | `compiler_bootstrap.gleam` | ✅ Now uses `test_api.run_test_file()` — reports errors |
| **test_api.gleam** | `src/tao/test_api.gleam` | ✅ Single source of truth for testing .tao files |
| ~~test_runner.gleam~~ | ~~src/tao/test_runner.gleam~~ | ❌ Deleted — was broken (stub desugaring) |


## Contact

- **GitHub**: Check repository for issues and discussions
- **Documentation**: See `docs/` directory for comprehensive guides
