# Exhaustiveness Checking Bug: Wildcard Pattern Not Recognized

> **Status**: 🐛 Bug identified, partial fix in progress
> **Date**: March 2026 (Updated)
> **Severity**: High - prevents wildcard patterns from working
> **Test Status**: 520/522 tests passing (99.6%)

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

**Workaround**: Use a variable pattern instead: `| n -> 100`

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

#### Issue 1: Grammar Structure Complexity

The match clause grammar uses `many(seq([...]))` which creates nested ListValue structures:

```gleam
many(seq([
  token_pattern("Pipe"),  // |
  ref("Pattern"),  // pattern
  opt(seq([...]))  // optional guard
  token_pattern("Arrow"),
  ref("Expr"),  // body
]))
```

This produces:
```
ListValue([
  ListValue([Pipe, Pattern, opt_if, Arrow, Body]),
  ListValue([Pipe, Pattern, opt_if, Arrow, Body]),
  ...
])
```

Where `Pattern` is an Expr that may be wrapped differently depending on how the pattern rules return values.

#### Issue 2: Pattern Rule Return Values

Pattern rules (`OrPattern`, `AsPattern`, `ConstructorPattern`, etc.) return `Expr` directly, but the grammar structure wraps them inconsistently:

- Some rules return `AstValue(Expr)`
- Some rules return `Expr` directly
- The `Pattern` rule needs to handle both cases

#### Issue 3: Pattern Extraction

The `extract_single_clause_from_list` function tries to extract patterns from the clause structure, but the wrapping varies:

```gleam
let pattern = case pattern_items {
  [AstValue(expr)] -> pattern_ast_to_pattern(expr)
  [ListValue([AstValue(expr)])] -> pattern_ast_to_pattern(expr)
  _ -> PWild(Span("error", 0, 0, 0, 0))  // Fallback produces error pattern
}
```

When the extraction fails, it returns `PWild(Span("error", ...))` instead of the actual pattern, causing the exhaustiveness checker to see an error pattern instead of `PAny`.

---

## Fix Plan

### Step 1: Simplify Pattern Rules ✅

Updated pattern rules to only handle `AstValue(Expr)` case:

```gleam
rule("Pattern", [
  alt(ref("OrPattern"), fn(values) {
    case values {
      [AstValue(e)] -> e  // Only handle AstValue case
      _ -> Int(0, Span("error", 0, 0, 0, 0))
    }
  }),
]),
```

### Step 2: Simplify Pattern Extraction

Update `extract_single_clause_from_list` to handle the actual grammar structure:

```gleam
fn extract_pattern_from_clause_items(items: List(Value(Expr)), pipe_pos: Int) -> Pattern {
  let pattern_items = list.drop(items, pipe_pos + 1) |> list.take(1)
  case pattern_items {
    [AstValue(expr)] -> pattern_ast_to_pattern(expr)
    [ListValue([AstValue(expr)])] -> pattern_ast_to_pattern(expr)
    _ -> PWild(Span("error", 0, 0, 0, 0))
  }
}
```

### Step 3: Debug Grammar Structure

Add debug output to see what structure is actually being produced for a simple wildcard pattern. This will help identify the exact wrapping pattern.

### Step 4: Fix Pattern Rules Consistently

Ensure all pattern rules (`OrPattern`, `AsPattern`, `ConstructorPattern`, `Tuple`, `List`) return values consistently wrapped in `AstValue`.

---

## Implementation Status

- [x] Added tests to reproduce the issue
- [x] Identified pattern extraction issue
- [x] Added handling for multiple ListValue wrapping levels
- [x] Simplified pattern rules to only handle AstValue case
- [x] Updated documentation with current status
- [ ] Debug grammar structure to see actual wrapping
- [ ] Fix all pattern rules to return consistent wrapping
- [ ] Verify fix works for all pattern types

---

## Related Documents

- **[docs/core.md](../core.md)** - Core language specification
- **[docs/plans/core/03-evaluator.md](./03-evaluator.md)** - Evaluator implementation
- **[src/core/core.gleam](../../src/core/core.gleam)** - Core language implementation (exhaustiveness checking)
- **[src/tao/syntax.gleam](../../src/tao/syntax.gleam)** - Tao syntax (pattern parsing)
- **[src/tao/desugar.gleam](../../src/tao/desugar.gleam)** - Tao desugarer (pattern conversion)

---

## Notes

The issue is complex because the grammar structure produces nested ListValue wrappers that vary depending on the pattern type. The fix requires understanding the exact structure being produced and updating both the pattern rules and the extraction logic to handle it consistently.

Current test status: **520/522 tests passing** (99.6%)
The 2 failures are pattern matching examples that fail due to this extraction issue.
