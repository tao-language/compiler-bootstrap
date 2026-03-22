# Codebase Maintenance Analysis

> **Goal**: Identify opportunities for simplification, refactoring, and removal of unnecessary complexity
> **Status**: 📋 Analysis Complete
> **Date**: March 2025

---

## Executive Summary

The codebase is **well-structured** but shows signs of rapid evolution with some duplication, overengineering, and incomplete features. The core language and syntax library are solid, but the CLI and Tao integration need work.

### Key Findings

| Category | Count | Priority |
|----------|-------|----------|
| Critical Issues | 3 | Fix immediately |
| High Priority | 8 | Fix within 2 weeks |
| Medium Priority | 12 | Fix within 1 month |
| Low Priority | 15 | Fix as time permits |

### Overall Health

- **Core Language**: ✅ Healthy (263 tests passing)
- **Syntax Library**: ✅ Healthy (well-tested)
- **Tao AST**: ⚠️ Incomplete (compiles but not integrated)
- **CLI**: ⚠️ Partial (basic functionality only)
- **Tests**: ⚠️ Inconsistent (some modules well-tested, others not)

---

## 1. Critical Issues

### 1.1 CLI Doesn't Actually Type Check or Evaluate

**File**: `src/compiler_bootstrap.gleam`

**Problem**: The `check_core` and `run_core` functions only parse, they don't actually type check or evaluate:

```gleam
fn check_core(file: File, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  // ... parsing ...
  
  // For now, just verify parsing works
  // Full type checking integration coming soon
  io.println("✓ Type checking " <> file.path)
  io.println("✓ No errors found")
  Ok(Nil)  // ← Always succeeds!
}
```

**Impact**: CLI gives false positives - reports "no errors" even for invalid programs.

**Fix**: Integrate with `core/core.gleam` type checker and evaluator.

**Priority**: 🔴 CRITICAL

---

### 1.2 Tao Desugaring Not Integrated

**Files**: `src/tao/desugar.gleam`, `src/compiler_bootstrap.gleam`

**Problem**: Tao desugaring exists but isn't wired up:

```gleam
fn check_tao(file: File, _verbose: Bool, _debug: Bool) -> Result(Nil, Error) {
  // Tao support not yet implemented
  io.println("✗ Tao language support not yet implemented")
  Error(RuntimeError("Tao not implemented"))
}
```

**Impact**: Can't test Tao language end-to-end.

**Fix**: Wire up Tao parser → desugar → core type checker pipeline.

**Priority**: 🔴 CRITICAL (blocks Tao development)

---

### 1.3 No Exit Codes

**File**: `src/compiler_bootstrap.gleam`

**Problem**: `main()` always returns `Nil`, never uses exit codes:

```gleam
pub fn main() {
  // ...
  Error(_) -> Nil  // ← Should be exit(1)
}
```

**Impact**: Can't use compiler in scripts or CI/CD pipelines.

**Fix**: Add `exit(0)` on success, `exit(1)` on error.

**Priority**: 🔴 CRITICAL

---

## 2. High Priority Issues

### 2.1 Overengineered Import System

**Files**: `src/tao/ast.gleam`

**Problem**: Import system is overly complex for current needs:

```gleam
pub type Import {
  Import(
    module: String,
    alias: Option(String),
    names: Option(ImportNames)
  )
}

pub type ImportNames {
  ImportAll
  ImportSome(List(ImportName))
}

pub type ImportName {
  ImportName(name: String, alias: Option(String))
}
```

**Issue**: 4 types just for imports! This is YAGNI - Tao modules aren't even implemented yet.

**Simplification**:
```gleam
pub type Import {
  Import(module: String, names: List(String))
}
// Import("math", ["min", "max"])
// Import("math", [])  // import math *
```

**Priority**: 🟠 HIGH

---

### 2.2 Duplicate Error Types

**Files**: `src/compiler_bootstrap.gleam`, `src/core/core.gleam`, `syntax/grammar.gleam`

**Problem**: Each module defines its own error types:

```gleam
// compiler_bootstrap.gleam
pub type Error {
  ParseError(errors: List(String))
  TypeError(message: String)
  RuntimeError(message: String)
  FileNotFound(path: String)
  // ...
}

// core/core.gleam
pub type Error {
  TypeMismatch(expected: Type, got: Type, span: Span)
  OccursCheck(id: Int, typ: Type)
  // ...
}

// syntax/grammar.gleam
pub type ParseError {
  ParseError(position: Int, expected: String, got: String)
}
```

**Issue**: No unified error handling, hard to compose.

**Fix**: Create unified error type in `src/error.gleam`:

```gleam
pub type Error {
  ParseError(span: Span, message: String)
  TypeError(span: Span, message: String)
  RuntimeError(span: Span, message: String)
  FileError(path: String, reason: String)
}
```

**Priority**: 🟠 HIGH

---

### 2.3 Unused Grammar DSL Features

**File**: `src/syntax/grammar.gleam`

**Problem**: Grammar DSL has features that aren't used:

```gleam
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,
    deconstructor: fn(a) -> List(Value(a)),  // ← Always panics!
    formatter: fn(a, Int) -> Doc,
  )
}
```

The `deconstructor` always panics:
```gleam
deconstructor: fn(_) { panic as "Deconstructor not implemented" }
```

**Issue**: Misleading API - suggests functionality that doesn't exist.

**Fix**: Remove `deconstructor` field until it's actually implemented.

**Priority**: 🟠 HIGH

---

### 2.4 Incomplete Literal Types

**File**: `src/core/core.gleam`

**Problem**: 6 literal types when Tao only needs 2:

```gleam
pub type Literal {
  I32(value: Int)
  I64(value: Int)
  U32(value: Int)
  U64(value: Int)
  F32(value: Float)
  F64(value: Float)
}
```

**Issue**: Tao wants untyped literals (`Int(Int)`, `Float(Float)`). Having 6 types creates unnecessary complexity.

**Fix**: Change to untyped literals as planned in `04-tao-integration.md`:

```gleam
pub type Literal {
  Int(Int)
  Float(Float)
}
```

**Priority**: 🟠 HIGH (blocks Tao integration)

---

### 2.5 No Pattern Guards in Core

**File**: `src/core/core.gleam`

**Problem**: `Case` type doesn't support guards:

```gleam
pub type Case {
  Case(pattern: Pattern, body: Term, span: Span)
}
```

**Issue**: Tao needs guards (`match x { | Some(y) if y > 0 -> y }`).

**Fix**: Add optional guard:

```gleam
pub type Case {
  Case(
    pattern: Pattern,
    guard: Option(Term),
    body: Term,
    span: Span
  )
}
```

**Priority**: 🟠 HIGH (blocks Tao pattern matching)

---

### 2.6 Verbose CLI Argument Parsing

**File**: `src/compiler_bootstrap.gleam`

**Problem**: Manual argument parsing is repetitive:

```gleam
fn parse_args(args: List(String)) -> Result(Command, String) {
  case args {
    [] -> Ok(Help)
    ["-h"] | ["--help"] -> Ok(Help)
    ["check", file, ..rest] -> {
      let verbose = list.contains(rest, "-v") || list.contains(rest, "--verbose")
      let debug = list.contains(rest, "--debug")
      Ok(Check(file, verbose, debug))
    }
    // ... repetitive ...
  }
}
```

**Fix**: Use a CLI library like `argv` more effectively or create a helper:

```gleam
fn has_flag(rest: List(String), short: String, long: String) -> Bool {
  list.contains(rest, short) || list.contains(rest, long)
}

// Usage:
let verbose = has_flag(rest, "-v", "--verbose")
```

**Priority**: 🟠 HIGH

---

### 2.7 Missing Module System Implementation

**Files**: `docs/plans/tao/`, `src/tao/ast.gleam`

**Problem**: AST defines imports but no implementation:

```gleam
pub type Program {
  Program(
    module: Option(String),
    imports: List(Import),
    declarations: List(Declaration),
  )
}
```

**Issue**: Can't actually import modules - not implemented anywhere.

**Recommendation**: Either implement it or remove from AST until ready.

**Priority**: 🟠 HIGH

---

### 2.8 Inconsistent Test Coverage

**Files**: `test/`

**Problem**: Wildly varying test coverage:

| Module | Tests | Status |
|--------|-------|--------|
| `core/core.gleam` | 263 | ✅ Excellent |
| `syntax/lexer.gleam` | 70 | ✅ Good |
| `syntax/grammar.gleam` | 37 | ⚠️ Basic |
| `syntax/formatter.gleam` | 36 | ⚠️ Basic |
| `tao/*` | 0 | ❌ None |
| `compiler_bootstrap.gleam` | 0 | ❌ None |

**Fix**: Add tests for CLI and Tao modules.

**Priority**: 🟠 HIGH

---

## 3. Medium Priority Issues

### 3.1 Overly Complex State Type

**File**: `src/core/core.gleam`

**Problem**: `State` has 8 fields, many rarely used:

```gleam
pub type State {
  State(
    hole: Int,        // Used
    var: Int,         // Used
    ctrs: CtrEnv,     // Rarely used
    ctx: Context,     // Used
    sub: Subst,       // Used
    errors: List(Error),  // Used
    ffi: FFI,         // Sometimes used
    config: Config,   // Rarely used
  )
}
```

**Simplification**: Split into `CoreState` and `ExtendedState`:

```gleam
pub type CoreState {
  CoreState(
    hole: Int,
    var: Int,
    ctx: Context,
    errors: List(Error)
  )
}

pub type FullState {
  FullState(
    core: CoreState,
    ctrs: CtrEnv,
    sub: Subst,
    ffi: FFI,
    config: Config
  )
}
```

**Priority**: 🟡 MEDIUM

---

### 3.2 Redundant Type Aliases

**File**: `src/core/core.gleam`

**Problem**: `pub type Type = Value` is confusing:

```gleam
pub type Type =
  Value
```

**Issue**: Why not just use `Value` everywhere? This alias suggests they're different when they're not.

**Fix**: Remove alias, use `Value` for both types and values (they're the same in dependent type theory).

**Priority**: 🟡 MEDIUM

---

### 3.3 Unused Constructor Fields

**File**: `src/core/core.gleam`

**Problem**: `Elim` has unused constructor:

```gleam
pub type Elim {
  EDot(name: String)      // Used
  EApp(arg: Value)        // Used
  EMatch(env: Env, motive: Value, cases: List(Case))  // ← Never constructed!
}
```

**Issue**: Dead code.

**Fix**: Remove `EMatch` until it's actually used.

**Priority**: 🟡 MEDIUM

---

### 3.4 Verbose Span Construction

**File**: Multiple files

**Problem**: Spans are verbose to construct:

```gleam
Span("input", 0, 0, 0, 0)  // Repeated everywhere
```

**Fix**: Add helper:

```gleam
pub fn dummy_span() -> Span {
  Span("input", 0, 0, 0, 0)
}

pub fn mk_span(file: String, line: Int, col: Int) -> Span {
  Span(file, line, col, line, col)
}
```

**Priority**: 🟡 MEDIUM

---

### 3.5 Inconsistent Naming

**Files**: Throughout codebase

**Problem**: Mixed naming conventions:

```gleam
// Snake case
pub type TermData { ... }
pub type LiteralType { ... }

// But then
pub fn desugar_expr()  // ✓
pub fn desugarBinOp()  // ✗ (not present, but watch for this)
```

**Fix**: Enforce snake_case consistently.

**Priority**: 🟡 MEDIUM

---

### 3.6 Missing Documentation Strings

**Files**: `src/tao/*`, `src/compiler_bootstrap.gleam`

**Problem**: Many public functions lack docstrings:

```gleam
pub fn desugar_expr(expr: ast.Expr) -> #(Term, List(DesugarError)) {
  // No docstring!
}
```

**Fix**: Add docstrings to all public functions.

**Priority**: 🟡 MEDIUM

---

### 3.7 Long Functions

**File**: `src/core/core.gleam`

**Problem**: Some functions are 200+ lines:

```gleam
pub fn infer(state: State, term: Term) -> #(Value, Type, State) {
  // 200+ lines of case branches
}
```

**Fix**: Extract helper functions:

```gleam
fn infer_lambda(state: State, name: String, body: Term) -> #(Value, Type, State) { ... }
fn infer_application(state: State, fun: Term, arg: Term) -> #(Value, Type, State) { ... }
```

**Priority**: 🟡 MEDIUM

---

### 3.8 Repeated Error Handling

**File**: `src/compiler_bootstrap.gleam`

**Problem**: Same error handling pattern repeated:

```gleam
case result {
  Ok(value) -> {
    case verbose {
      True -> io.println("✓ Success")
      False -> Nil
    }
    Ok(value)
  }
  Error(err) -> {
    report_error(err)
    Error(err)
  }
}
```

**Fix**: Create helper:

```gleam
fn with_verbose<T>(
  result: Result(T, Error),
  verbose: Bool,
  success_msg: String,
) -> Result(T, Error) {
  case result {
    Ok(value) -> {
      case verbose {
        True -> io.println(success_msg)
        False -> Nil
      }
      Ok(value)
    }
    Error(err) -> {
      report_error(err)
      Error(err)
    }
  }
}
```

**Priority**: 🟡 MEDIUM

---

### 3.9 Unused Imports

**Files**: Multiple

**Problem**: Unused imports not removed:

```gleam
import gleam/option.{type Option, None, Some}  // Only Some used
```

**Fix**: Clean up imports.

**Priority**: 🟡 MEDIUM

---

### 3.10 Magic Numbers

**Files**: `src/syntax/formatter.gleam`

**Problem**: Hardcoded width:

```gleam
pub fn render_default(doc: Doc) -> String {
  render(doc, 80)  // Why 80?
}
```

**Fix**: Make configurable or document why 80.

**Priority**: 🟡 MEDIUM

---

### 3.11 Incomplete Type Definitions

**File**: `src/tao/ast.gleam`

**Problem**: Types defined but not used:

```gleam
pub type ConstructorField {
  NamedField(name: String, type_: Type)
  UnnamedField(type_: Type)
}
```

**Issue**: These aren't used anywhere in desugaring yet.

**Fix**: Either use them or remove until needed.

**Priority**: 🟡 MEDIUM

---

### 3.12 Verbose Error Reporting

**File**: `src/compiler_bootstrap.gleam`

**Problem**: Error reporting is basic string concatenation:

```gleam
fn report_error(error: Error) {
  case error {
    ParseError(errors) -> {
      io.println("✗ Parse errors:")
      errors |> list.each(fn(e) { io.println("  " <> e) })
    }
    // ...
  }
}
```

**Fix**: Implement proper error reporter as planned in `docs/plans/cli/03-error-reporter.md`.

**Priority**: 🟡 MEDIUM

---

## 4. Low Priority Issues

### 4.1 Over-Commented Code

**File**: `src/core/core.gleam`

**Problem**: Some comments state the obvious:

```gleam
/// Bound variable using De Bruijn index (distance to binder)
Var(index: Int)
```

**Fix**: Remove obvious comments, keep only non-obvious ones.

**Priority**: 🟢 LOW

---

### 4.2 Inconsistent Error Message Format

**Files**: Throughout

**Problem**: Mixed error message styles:

```gleam
"Expected $Type, got $I32"  // One style
"Variable 'x' not in scope"  // Another style
```

**Fix**: Standardize error message format.

**Priority**: 🟢 LOW

---

### 4.3 Unused Helper Functions

**File**: `src/syntax/grammar.gleam`

**Problem**: Helper functions defined but never called:

```gleam
fn fold_operators(...) { ... }  // Defined but not used
```

**Fix**: Remove or use.

**Priority**: 🟢 LOW

---

### 4.4 Verbose Type Annotations

**File**: Multiple

**Problem**: Over-annotated when inference works:

```gleam
let result: Result(Term, Error) = parse_term(source)
```

**Fix**: Let Gleam infer:

```gleam
let result = parse_term(source)
```

**Priority**: 🟢 LOW

---

### 4.5 Redundant Pattern Matches

**File**: Multiple

**Problem**: Matching when not needed:

```gleam
case boolean_value {
  True -> do_something()
  False -> Nil
}
```

**Fix**: Use `if`:

```gleam
if boolean_value { do_something() }
```

**Priority**: 🟢 LOW

---

### 4.6 Missing Examples

**Files**: `src/examples/`

**Problem**: Only `calc.gleam` example exists.

**Fix**: Add more examples showing different features.

**Priority**: 🟢 LOW

---

### 4.7 Inconsistent Module Headers

**Files**: Throughout

**Problem**: Some files have elaborate headers, others don't:

```gleam
// ============================================================================
// FORMATTER - Document Algebra Pretty Printer
// ============================================================================
```

vs.

```gleam
import gleam/list
```

**Fix**: Standardize or remove all.

**Priority**: 🟢 LOW

---

### 4.8 Test Duplication

**Files**: `test/core/core_test.gleam`

**Problem**: Similar tests repeated with minor variations.

**Fix**: Use test helpers or parameterized tests.

**Priority**: 🟢 LOW

---

### 4.9 Verbose Debug Output

**File**: `src/compiler_bootstrap.gleam`

**Problem**: Debug output uses `inspect()`:

```gleam
fn debug_term(term: Term) -> String {
  syntax.format(term)  // Not very debuggable
}
```

**Fix**: Create proper debug printer.

**Priority**: 🟢 LOW

---

### 4.10 Missing Performance Notes

**Files**: Throughout

**Problem**: No documentation of performance characteristics.

**Fix**: Add comments for non-obvious performance considerations.

**Priority**: 🟢 LOW

---

### 4.11 Incomplete TODO Comments

**Files**: Multiple

**Problem**: TODOs without context:

```gleam
// TODO: Fix this
```

**Fix**: Add context and links to issues.

**Priority**: 🟢 LOW

---

### 4.12 Unused Type Parameters

**File**: `src/syntax/grammar.gleam`

**Problem**: Type parameters that don't vary:

```gleam
pub type Pattern(a) {
  // 'a' is used in constructors but often ignored
}
```

**Fix**: Consider if polymorphism is needed.

**Priority**: 🟢 LOW

---

### 4.13 Verbose Function Chains

**File**: Multiple

**Problem**: Long pipe chains:

```gleam
source
|> tokenize
|> parse
|> type_check
|> desugar
|> evaluate
```

**Fix**: Extract named intermediate steps.

**Priority**: 🟢 LOW

---

### 4.14 Missing Benchmarks

**Files**: None exist

**Problem**: No performance benchmarks.

**Fix**: Add basic benchmarks for key operations.

**Priority**: 🟢 LOW

---

### 4.15 Inconsistent Spacing

**Files**: Throughout

**Problem**: Mixed spacing around operators:

```gleam
let x=5  // No spaces
let y = 10  // Spaces
```

**Fix**: Run formatter or enforce style guide.

**Priority**: 🟢 LOW

---

## 5. Recommended Refactoring Order

### Week 1: Critical Fixes

1. **Add exit codes to CLI** (1.3) - 1 hour
2. **Wire up type checking in CLI** (1.1) - 4 hours
3. **Integrate Tao desugaring** (1.2) - 8 hours

### Week 2: High Priority

4. **Simplify import types** (2.1) - 2 hours
5. **Create unified error type** (2.2) - 4 hours
6. **Remove unused deconstructor** (2.3) - 1 hour
7. **Implement untyped literals** (2.4) - 4 hours
8. **Add pattern guards** (2.5) - 3 hours

### Week 3-4: Medium Priority

9. **Split State type** (3.1) - 4 hours
10. **Remove Type alias** (3.2) - 1 hour
11. **Clean up unused code** (3.3, 4.3) - 2 hours
12. **Add span helpers** (3.4) - 1 hour
13. **Add docstrings** (3.6) - 4 hours
14. **Refactor long functions** (3.7) - 6 hours

### Month 2: Polish

15. **Add CLI tests** (2.8) - 4 hours
16. **Add Tao tests** (2.8) - 8 hours
17. **Implement error reporter** (3.12) - 6 hours
18. **Clean up remaining issues** - 8 hours

---

## 6. Code Quality Metrics

### Current State

| Metric | Value | Target |
|--------|-------|--------|
| Total Lines | ~6000 | - |
| Test Coverage | ~60% | 80% |
| Public Functions | ~200 | - |
| Documented Functions | ~40% | 90% |
| Average Function Length | 25 lines | <20 |
| Max Function Length | 200+ lines | <50 |

### After Refactoring (Target)

| Metric | Target |
|--------|--------|
| Test Coverage | 80%+ |
| Documented Functions | 90%+ |
| Critical Issues | 0 |
| High Priority Issues | 0 |
| Build Time | <5 seconds |
| Test Time | <30 seconds |

---

## 7. Conclusion

The codebase is **fundamentally sound** but needs focused cleanup:

1. **Fix critical issues first** - CLI doesn't work, no exit codes
2. **Remove unused features** - Deconstructors, EMatch, etc.
3. **Simplify overengineered parts** - Import system, State type
4. **Add missing tests** - CLI, Tao modules
5. **Complete planned features** - Untyped literals, pattern guards

**Estimated total effort**: 80-100 hours over 6-8 weeks.

**Confidence**: **90%** - Issues are well-understood, fixes are straightforward.
