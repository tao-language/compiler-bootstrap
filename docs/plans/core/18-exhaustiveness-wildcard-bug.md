# Exhaustiveness Checking Bug: Wildcard Pattern Not Recognized

> **Status**: 🐛 Bug identified, fix in progress
> **Date**: March 2026
> **Severity**: High - prevents wildcard patterns from working

---

## Problem Description

Wildcard patterns (`_`) in match expressions are not being recognized as exhaustive, even though they should cover all cases.

**Example**:
```tao
let x = 100
match x {
  | _ -> 100  // Error: Pattern match not exhaustive
}
```

**Expected**: No error (wildcard covers all cases)
**Actual**: `error[E0202]: Pattern match not exhaustive`

---

## Root Cause Analysis

### Pattern Conversion Pipeline

The pattern goes through multiple conversion stages:

1. **Parsing** (`src/tao/syntax.gleam`):
   - Source `_` → `Var("_", span)` (Expr)
   - `pattern_ast_to_pattern(Var("_", span))` → `PWild(span)` (syntax.Pattern)

2. **AST Conversion** (`src/tao/syntax.gleam`):
   - `pattern_to_ast(PWild(span))` → `AstPAny(span)` (ast.Pattern)

3. **Desugaring** (`src/tao/desugar.gleam`):
   - `tao_pattern_to_core_pattern(AstPAny(span))` → `core.PAny` (core.Pattern)

4. **Exhaustiveness Checking** (`src/core/core.gleam`):
   - `check_exhaustiveness` checks if last case has `pattern: PAny`

### Identified Issues

#### Issue 1: Pattern Extraction in `extract_single_clause_from_list`

The function extracts patterns from match clauses but may not handle all grammar structures correctly:

```gleam
let pattern_items = list.drop(items, pos + 1) |> list.take(1)
let pattern = case pattern_items {
  [AstValue(expr)] -> pattern_ast_to_pattern(expr)
  [ListValue([AstValue(expr)])] -> pattern_ast_to_pattern(expr)  // Added
  _ -> PWild(Span("error", 0, 0, 0, 0))
}
```

**Problem**: The pattern might be wrapped in additional `ListValue` layers due to the grammar structure, causing the extraction to fail and return `PWild(Span("error", ...))` instead of the actual pattern.

#### Issue 2: Grammar Structure Mismatch

The `OrPattern` rule uses `many()` which wraps results in `ListValue`:

```gleam
rule("OrPattern", [
  alt(
    seq([
      ref("AsPattern"),
      many(seq([token_pattern("Pipe"), ref("AsPattern")])),
    ]),
    fn(values) {
      case values {
        [AstValue(first), rest, ..] -> {
          // rest is ListValue([ListValue([Pipe, AsPattern]), ...])
          ...
        }
        ...
      }
    },
  ),
]),
```

For a simple wildcard, the structure is:
- `OrPattern` returns `AstValue(Var("_", span))`
- `Pattern` rule wraps this: `AstValue(AstValue(Var("_", span)))`

This double-wrapping causes the extraction to fail.

#### Issue 3: `check_exhaustiveness` Pattern Matching

The `check_exhaustiveness` function checks for specific pattern types:

```gleam
case list.last(cases) {
  Ok(Case(pattern: PAny, guard: None, ..)) -> redundant_errors
  Ok(Case(pattern: PAs(PAny, _), guard: None, ..)) -> redundant_errors
  _ -> { /* continue with exhaustiveness checking */ }
}
```

If the pattern is not exactly `PAny` or `PAs(PAny, _)`, the function continues with exhaustiveness checking, which produces the error.

---

## Fix Plan

### Step 1: Fix Pattern Extraction

Update `extract_single_clause_from_list` to handle all possible grammar structures:

```gleam
fn extract_single_clause_from_list(items: List(Value(Expr))) -> Option(MatchClause) {
  let pipe_pos = find_pipe_position(items, 0)
  case pipe_pos {
    Some(pos) -> {
      // Extract pattern, handling various wrapping levels
      let pattern = extract_pattern_from_items(items, pos)
      ...
    }
    None -> None
  }
}

fn extract_pattern_from_items(items: List(Value(Expr)), pipe_pos: Int) -> Pattern {
  let pattern_items = list.drop(items, pipe_pos + 1) |> list.take(1)
  case pattern_items {
    [AstValue(expr)] -> pattern_ast_to_pattern(expr)
    [ListValue([AstValue(expr)])] -> pattern_ast_to_pattern(expr)
    [ListValue([ListValue([AstValue(expr)])])] -> pattern_ast_to_pattern(expr)
    _ -> PWild(Span("error", 0, 0, 0, 0))
  }
}
```

### Step 2: Simplify Grammar Structure

Consider simplifying the `OrPattern` rule to avoid double-wrapping:

```gleam
// Instead of using many(), use a simpler structure
rule("OrPattern", [
  alt(
    seq([ref("AsPattern")]),  // Single pattern without wrapping
    seq([ref("AsPattern"), many(seq([token_pattern("Pipe"), ref("AsPattern")]))]),
  ),
  fn(values) { ... }
]),
```

### Step 3: Add Debug Pattern Matching

Add more comprehensive pattern matching in `check_exhaustiveness` to identify what patterns are actually being produced:

```gleam
Ok(Case(pattern: p, guard: g, ..)) -> {
  case p {
    PAny -> redundant_errors
    PAs(PAny, _) -> redundant_errors
    // Add more cases to identify the actual pattern
    PAs(inner, _) -> {
      case inner {
        PAny -> redundant_errors
        _ -> { /* continue */ }
      }
    }
    _ -> { /* continue */ }
  }
}
```

### Step 4: Add Tests

Add comprehensive tests for exhaustiveness checking:

```gleam
// Test wildcard is exhaustive
pub fn match_exhaustiveness_wildcard_is_exhaustive_test() {
  let motive = lam("p", i32t(s0), s0)
  let cases = [case_(pany(), i32(100, s1), s1)]
  let term = match_(i32(5, s2), motive, cases, s3)
  let #(_, _, state) = c.infer(s, term)
  // Should NOT have exhaustiveness error
  list.any(state.errors, fn(e) {
    case e { c.MatchMissingCase(_, _) -> True; _ -> False }
  }) |> should.be_false
}

// Test as-pattern with wildcard is exhaustive
pub fn match_exhaustiveness_as_wildcard_is_exhaustive_test() {
  let motive = lam("p", i32t(s0), s0)
  let cases = [case_(c.PAs(c.PAny, "x"), i32(100, s1), s1)]
  let term = match_(i32(5, s2), motive, cases, s3)
  let #(_, _, state) = c.infer(s, term)
  // Should NOT have exhaustiveness error
  list.any(state.errors, fn(e) {
    case e { c.MatchMissingCase(_, _) -> True; _ -> False }
  }) |> should.be_false
}

// Test missing wildcard produces error
pub fn match_exhaustiveness_missing_case_test() {
  let motive = lam("p", i32t(s0), s0)
  let cases = [case_(c.PLit(c.I32(0)), i32(1, s1), s1)]
  let term = match_(i32(5, s2), motive, cases, s3)
  let #(_, _, state) = c.infer(s, term)
  // Should have exhaustiveness error
  list.any(state.errors, fn(e) {
    case e { c.MatchMissingCase(_, _) -> True; _ -> False }
  }) |> should.be_true
}
```

---

## Implementation Status

- [x] Added tests to reproduce the issue
- [x] Identified pattern extraction issue in `extract_single_clause_from_list`
- [x] Added handling for `ListValue` wrapped patterns
- [ ] Verify fix works for all pattern types
- [ ] Simplify grammar structure if needed
- [ ] Add more comprehensive tests
- [ ] Update documentation

---

## Related Documents

- **[docs/core.md](../core.md)** - Core language specification
- **[docs/plans/core/03-evaluator.md](./03-evaluator.md)** - Evaluator implementation
- **[src/core/core.gleam](../../src/core/core.gleam)** - Core language implementation (exhaustiveness checking)
- **[src/tao/syntax.gleam](../../src/tao/syntax.gleam)** - Tao syntax (pattern parsing)
- **[src/tao/desugar.gleam](../../src/tao/desugar.gleam)** - Tao desugarer (pattern conversion)

---

## Notes

The issue appears to be in the pattern extraction logic, not in the exhaustiveness checking itself. The `check_exhaustiveness` function correctly identifies `PAny` as exhaustive, but the pattern is not being converted to `PAny` correctly.

The fix requires careful handling of the grammar structure to ensure patterns are extracted correctly regardless of how they're wrapped by the grammar rules.
