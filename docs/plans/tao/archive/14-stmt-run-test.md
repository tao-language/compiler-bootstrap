# Stmt System: Run and Test Statements

> **Goal**: Support top-level expressions and tests in Tao modules without special syntax
> **Status**: 📋 Planned
> **Date**: March 16, 2026 (updated March 16, 2026)

---

## Status

### What's Working

- Program parsing without `Block` wrapper for single expressions
- `StmtExpr(value, span)` for expression statements (equivalent to `Run`)
- Basic statement types: `StmtLet`, `StmtFn`, `StmtImport`, `StmtExpr`
- `let mut` parsing fixed
- Round-trip formatting for basic expressions (numbers, variables, binary ops)

### What's Pending

- Rename `StmtExpr` to `Run` and remove span (expr has span)
- `Test(name: String, expr: Expr, expected: Pattern)` statement type for tests
- REPL-style test syntax:
  ```tao
  -- test test_name
  > expr
  result_pattern
  ```
- Module resolution ignoring `Run` and `Test` statements
- CLI `run` command executing `Run` statements
- CLI `test` command executing `Test` statements with pattern matching
- Formatter support for `Run` and `Test` statements
- Grammar features:
  - Unary negation (`-5`)
  - Error recovery (`let x = ;`)

### Related

- See **[01-overview.md](./01-overview.md)** for overall Tao status
- See **[03-desugaring.md](./03-desugaring.md)** for desugaring rules
- See **[11-test-system.md](./11-test-system.md)** for test system specification
- See **[13-stmt-system.md](./13-stmt-system.md)** for original Stmt design

---

## Overview

### Core Principle

**Tao modules should work like scripts** - you can write expressions at top level and they get evaluated, just like Python, TypeScript, or a REPL.

### Current Problem

Currently, a Tao program is parsed as `Block(Expr)`, which means:
- Input `"42"` becomes `Block([Int(42)])` (type mismatch - Block expects Stmt)
- Formatter outputs `"{ 42 }"` instead of `"42"`
- No way to distinguish "definitions" from "expressions to evaluate"

### Proposed Solution

Introduce two new statement types:

```gleam
pub type Stmt {
  // ... existing: Let, Fn, Import, Type, etc.
  Run(expr: Expr)                    // Expression to evaluate (span from expr)
  Test(name: String, expr: Expr, expected: Pattern)  // Test with expected pattern
}
```

Now a program is simply `List(Stmt)`:
- `42` → `[Run(Int(42, span))]`
- `let x = 42` → `[StmtLet("x", False, None, Int(42, span), span)]`
- Test syntax:
  ```tao
  -- test identity
  > id(42)
  42
  ```
  → `[Test("identity", App(Var("id", _), [Int(42, _)], _), PLit(42, _), span)]`

---

## Design Decisions

### 1. Program = List(Stmt)

**Decision**: Remove the `Block` wrapper entirely. A program is just a list of statements.

**Rationale**:
- Simpler AST - no artificial wrapping
- Each statement knows if it should be "run" or is just a definition
- Matches how modules work conceptually

### 2. Run(Expr) for Top-Level Expressions

**Decision**: Wrap bare expressions in `Run` statements. No separate span needed.

**Rationale**:
- Distinguishes expressions-to-evaluate from definitions
- Expression already carries span for error reporting
- Allows mixing definitions and expressions naturally

### 3. Test(name, expr, expected) for REPL-Style Tests

**Decision**: Use `-- test name` followed by `> expr` and `result_pattern` (REPL-style).

**Syntax**:
```tao
-- test identity function
> let id = fn(x) { x } in id(42)
42

-- test addition
> 1 + 2
3
```

**Rationale**:
- Familiar to anyone who's used a REPL
- Test name provides documentation
- Expected pattern enables powerful matching (not just equality)
- Visually distinct from regular code

### 4. Test Desugaring to Pattern Match

**Decision**: Tests desugar to pattern matching:
```gleam
Test(name, expr, expected) 
  → match expr { 
      expected -> Pass(span, name) 
      | got -> Fail(span, name, got) 
    }
```

**Rationale**:
- Leverages existing pattern matching
- Provides detailed failure information (what we got vs expected)
- Patterns are more expressive than simple equality

### 5. Module Resolution Ignores Run/Test

**Decision**: When building the module's definition record (for imports/type-checking), ignore `Run` and `Test` statements.

**Rationale**:
- Tests and "script output" aren't part of the module's API
- Matches how other languages work (Python `if __name__ == "__main__"` is separate from module definitions)

### 6. CLI Separation

**Decision**: 
- `gleam run file.tao` - Executes `Run` statements, ignores `Test`
- `gleam test file.tao` - Executes `Test` statements, ignores `Run`
- `gleam check file.tao` - Type-checks everything (including Run/Test bodies)

**Rationale**:
- Clear separation of concerns
- Tests don't run during normal execution
- Script output doesn't interfere with test results

---

## Syntax

### Grammar Changes

```
Program = Stmt*

Stmt 
  = Import
  | Fn
  | Let
  | Type
  | Test      // "-- test name" followed by "> expr" and "pattern"
  | Run       // Expr (bare expression at statement position)

Test = "--" "test" Ident "\n" ">" Expr "\n" Pattern

Run = Expr  // Any expression at statement position
```

### Examples

| Input | Parsed As |
|-------|-----------|
| `42` | `[Run(Int(42, span))]` |
| `let x = 42` | `[StmtLet("x", False, None, Int(42, span), span)]` |
| `-- test identity\n> id(42)\n42` | `[Test("identity", App(Var("id"), [Int(42)]), PLit(42), span)]` |
| `fn f() { 1 }; f()` | `[StmtFn(...), Run(App(Var("f"), []))]` |

---

## Implementation Plan

### Phase 1: AST Changes

1. Add `Run(expr: Expr)` to `Stmt` type in `src/tao/ast.gleam`
2. Add `Test(name: String, expr: Expr, expected: Pattern, span: Span)` to `Stmt` type
3. Update parser to recognize `-- test name` followed by `> expr` and pattern
4. Update parser to wrap bare expressions as `Run`

### Phase 2: Formatter

1. Format `Run(expr)` as just the expression (no wrapper)
2. Format `Test(name, expr, expected)` as:
   ```
   -- test {name}
   > {expr}
   {expected}
   ```
3. Update round-trip tests

### Phase 3: Module Resolution

1. Update `build_module_definitions()` to filter out `Run` and `Test`
2. Ensure imports/type-checking only see definitions

### Phase 4: Desugaring

1. Desugar `Test(name, expr, expected)` to pattern match:
   ```gleam
   match expr {
     expected -> #Pass(name)
     | got -> #Fail(name, got)
   }
   ```
2. Add `Pass` and `Fail` constructors to standard library

### Phase 5: CLI Integration

1. `run` command: Execute `Run` statements, print results
2. `test` command: Execute `Test` statements, report pass/fail
3. `check` command: Type-check all statements

### Phase 6: Testing

1. Update existing syntax tests (expect no `{}` wrapper)
2. Add tests for `Run` statements
3. Add tests for `Test` statements
4. Add integration tests for CLI commands

---

## Known Issues and Tradeoffs

### Issue: Expression vs Statement Ambiguity

**Problem**: How do we distinguish `let x = 42` (a Let statement) from `42` (a Run statement)?

**Solution**: The parser already handles this - `let` is a keyword that starts a Let rule. If parsing as Let fails, try parsing as Expr and wrap in Run.

### Issue: Test Pattern Parsing

**Problem**: Patterns can span multiple lines (e.g., record patterns), making it tricky to know where the pattern ends.

**Solution**: 
- Option A: Pattern ends at next `-- test`, `>`, or EOF
- Option B: Use indentation to determine pattern extent
- Option C: Require patterns to be single-line for tests

**Decision**: Start with Option A - pattern continues until next test marker or EOF.

### Tradeoff: No Explicit "Main" Function

**Decision**: Unlike languages with explicit `main()`, Tao runs all top-level expressions.

**Pros**:
- Simpler for scripting
- No boilerplate for simple programs

**Cons**:
- Less explicit about entry point
- All top-level code runs on import (like Python, unlike ML)

### Tradeoff: Test Syntax

**Decision**: Use `-- test name` + `> expr` + `pattern` (REPL-style) instead of `#test` or `@test` attribute.

**Pros**:
- Minimal syntax
- Feels like trying things in REPL
- Pattern matching is more expressive than assertions
- Easy to comment out tests (just prefix with `//`)

**Cons**:
- Less discoverable than keyword
- Multi-line patterns may be ambiguous

---

## Alternatives Considered

### Alternative 1: Keep Block Wrapper

```gleam
Program = Block(Stmt)
```

**Rejected because**:
- Artificial wrapping adds complexity
- Formatter needs to strip braces for single expressions
- Doesn't solve the "what to execute" problem

### Alternative 2: Explicit `run` Keyword

```tao
run 42
run add(1, 2)
```

**Rejected because**:
- Verbose for scripting
- Unnecessary keyword for obvious intent

### Alternative 3: Semicolon-Terminated Statements

```tao
let x = 42;
42;
> 1 + 1;
```

**Rejected because**:
- Gleam/ML style doesn't require semicolons
- Adds syntactic noise

### Alternative 4: Separate Test Files

Keep tests in separate `*_test.tao` files only.

**Rejected because**:
- Inline tests are valuable for documentation
- REPL-style testing is more interactive
- Examples in docs can be runnable tests

### Alternative 5: Assert-Style Tests

```tao
test "identity" { assert_eq(id(42), 42) }
```

**Rejected because**:
- More verbose than REPL-style
- Less flexible than pattern matching
- Doesn't look like a REPL session

---

## Open Questions

1. **Should `Run` statements have optional names for debugging?**
   - `run "identity test" { id(42) }`
   - Pro: Better error messages
   - Con: More verbose

2. **Should test output show expected vs actual?**
   - Already handled by pattern match desugaring - `Fail(name, got)` contains both

3. **Should there be a way to suppress Run output?**
   - `42;` (semicolon means "don't print")
   - Pro: More control
   - Con: Semicolons feel un-Gleam-like

4. **How to handle multi-line patterns in tests?**
   - Decision: Pattern continues until next `-- test`, `>`, or EOF
   - May need indentation sensitivity for complex patterns

---

## Implementation Details

### AST Changes

```gleam
// src/tao/ast.gleam
pub type Stmt {
  // ... existing
  Run(expr: Expr)
  Test(name: String, expr: Expr, expected: Pattern, span: Span)
}
```

### Parser Changes

The parser currently has:
```gleam
rule("Stmt", [
  alt(ref("Import"), ...),
  alt(ref("Fn"), ...),
  alt(ref("Let"), ...),
  alt(ref("Expr"), fn(values) { ... }),  // This becomes Run
])
```

Change to:
```gleam
rule("Stmt", [
  alt(ref("Import"), ...),
  alt(ref("Fn"), ...),
  alt(ref("Let"), ...),
  // Test: "--" "test" name "\n" ">" expr "\n" pattern
  alt(
    seq([
      token_pattern("Dash"),
      token_pattern("Dash"),
      keyword_pattern("test"),
      token_pattern("Ident"),  // name
      token_pattern("Newline"),
      token_pattern("Greater"),  // ">"
      ref("Expr"),
      token_pattern("Newline"),
      ref("Pattern"),
    ]),
    fn(values) { Test(name, expr, pattern, span) },
  ),
  // Run: bare Expr
  alt(ref("Expr"), fn(values) { Run(expr) }),
])
```

### Formatter Changes

```gleam
fn format_stmt(stmt: Stmt) -> String {
  case stmt {
    Run(expr) -> format_expr(expr)
    Test(name, expr, expected, _) -> 
      "-- test " <> name <> "\n> " <> format_expr(expr) <> "\n" <> format_pattern(expected)
    // ... other cases
  }
}
```

### Desugaring Changes

```gleam
// src/tao/desugar.gleam
fn desugar_stmt(stmt: Stmt) -> CoreTerm {
  case stmt {
    Run(expr) -> desugar_expr(expr)
    Test(name, expr, expected, span) -> {
      let core_expr = desugar_expr(expr)
      let core_pattern = desugar_pattern(expected)
      // Build: match expr { pattern -> Pass(name) | got -> Fail(name, got) }
      build_test_match(core_expr, core_pattern, name, span)
    }
    // ... other cases
  }
}
```

### Module Resolution Changes

```gleam
fn build_module_definitions(stmts: List(Stmt)) -> Definitions {
  stmts
  |> list.filter(fn(stmt) {
    case stmt {
      Run(_) | Test(_, _, _, _) -> False  // Skip
      _ -> True  // Keep Let, Fn, Type, Import, etc.
    }
  })
  |> ...  // Build definitions as before
}
```

---

## Testing Strategy

### Unit Tests

1. **Parser tests**: Verify `Run` and `Test` parsing
2. **Formatter tests**: Round-trip for new statement types
3. **Module resolution tests**: Verify Run/Test are filtered
4. **Desugaring tests**: Verify Test becomes pattern match

### Integration Tests

1. **CLI run**: Verify Run statements execute
2. **CLI test**: Verify Test statements execute and report pass/fail
3. **CLI check**: Verify type-checking includes Run/Test bodies

### Example Test Cases

```tao
// File: examples/tao/run_example.tao
let x = 42
x  // Should print 42

fn add(a, b) { a + b }
add(1, 2)  // Should print 3
```

```tao
// File: examples/tao/test_example.tao
fn add(a, b) { a + b }

-- test addition
> add(1, 2)
3

-- test with variable pattern
> add(5, 3)
result  // Matches any value, binds to 'result'
```

```tao
// File: examples/tao/test_pattern_example.tao
fn make_pair(a, b) { #Pair(a, b) }

-- test pair construction
> make_pair(1, 2)
#Pair(1, 2)
```

---

## Future Work

1. **Test groups**: Organize tests with labels
   ```tao
   -- test "arithmetic.add"
   > add(1, 2)
   3
   ```

2. **Test guards**: Conditional test execution
   ```tao
   -- test "only on 64-bit" if comptime { target_bits == 64 }
   > large_number()
   9223372036854775807
   ```

3. **Run guards**: Conditional execution
   ```tao
   if comptime { debug_print("hello") }
   ```

4. **Main function convention**: Recognize `main()` as entry point
   ```tao
   fn main() { run_all_tests() }
   ```

5. **Test output capture**: Capture stdout for comparison
   ```tao
   -- test "prints hello"
   > print("hello")
   @output "hello\n"
   ```

---

## Change Log

| Date | Change |
|------|--------|
| 2026-03-16 | Initial plan created |
| 2026-03-16 | Updated Test to include name and expected pattern, REPL-style syntax |
| 2026-03-16 | Fixed Program rule to not wrap single expressions in Block |
| 2026-03-16 | Fixed `let mut` parsing (KeywordValue vs TokenValue) |
| 2026-03-16 | Fixed core lambda generalization - implicit type variables now instantiated during application |
