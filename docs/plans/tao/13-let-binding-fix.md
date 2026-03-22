# Let Binding Implementation Plan

> **Status**: 📋 Planning (partial implementation in progress)
> **Date**: March 15, 2026

---

## Current Status

### What's Done

1. ✅ Added `Let` constructor to `Expr` type in `src/tao/syntax.gleam`
2. ✅ Grammar rule for `let` bindings in place
3. ✅ `make_let()` helper function (partially implemented)
4. ✅ `expr_to_ast()` handles `Let` (placeholder)
5. ✅ `format_expr_loop()` formats `Let` expressions
6. ✅ `exprs_to_stmts()` converts `Let` to `StmtLet`

### What's Broken

1. ❌ `make_let()` has type errors - doesn't handle `opt()` return values correctly
2. ❌ Missing `Let` pattern in `get_expr_span()` functions (lines 276, 535)
3. ❌ `lexer.Keyword` constructor doesn't exist

---

## Issues to Fix

### 1. Grammar `opt()` Semantics

The grammar's `opt(pattern)` returns values differently than expected:
- When present: includes the matched values in the sequence
- When absent: skips those values entirely (no `None` wrapper)

This means a sequence like:
```gleam
seq([
  keyword_pattern("let"),
  opt(keyword_pattern("mut")),
  token_pattern("Ident"),
  opt(seq([token_pattern("Colon"), token_pattern("Ident")])),
  token_pattern("="),
  ref("Expr"),
])
```

Produces different length value lists:
- With type: `["let", mut_opt, name, type, "=", expr]` (6 values)
- Without type: `["let", mut_opt, name, "=", expr]` (5 values)

**Solution**: Handle variable-length sequences in `make_let()`.

### 2. Missing `Let` Pattern in `get_expr_span()`

Two functions need the `Let` case:
- `get_expr_span()` around line 276
- Another span function around line 535

**Solution**: Add `Let(_, _, _, _, span) -> span` case to both.

### 3. `lexer.Keyword` Doesn't Exist

The `tao/lexer` module doesn't export a `Keyword` constructor.

**Solution**: Use `Span("error", 0, 0, 0, 0)` directly for error cases, or find the correct constructor.

---

## Implementation Steps

### Step 1: Fix `get_expr_span()` Functions

Add `Let` case to both span functions:

```gleam
fn get_expr_span(expr: Expr) -> Span {
  case expr {
    // ... existing cases ...
    Let(_, _, _, _, span) -> span
  }
}
```

### Step 2: Fix `make_let()` Variable-Length Handling

The key insight is that `opt()` doesn't wrap in `Option` - it just includes/excludes values.

```gleam
fn make_let(values) -> Expr {
  // Handle both 5 and 6 element cases
  case list.length(values) {
    6 -> {
      // Has type annotation: [_, mut_opt, name, type, "=", expr]
      // Extract accordingly
    }
    5 -> {
      // No type annotation: [_, mut_opt, name, "=", expr]
      // Extract accordingly
    }
    _ -> panic as "Unexpected let binding structure"
  }
}
```

### Step 3: Fix Error Handling

Replace `lexer.Keyword(...)` with proper error values:
```gleam
// Instead of:
lexer.Keyword("name", Span("error", 0, 0, 0, 0))

// Use:
// Just panic or use a default TokenValue
```

---

## Testing

After fixes, test with:
```tao
// Simple let
let x = 10
x

// Let with mut
let mut y = 20
y

// Let with type
let z: Int = 30
z

// Let with mut and type
let mut w: Int = 40
w
```

Expected outputs: `10`, `20`, `30`, `40`

---

## Related Files

- `src/tao/syntax.gleam` - Grammar and `make_let()`
- `src/tao/ast.gleam` - `StmtLet` type
- `src/compiler_bootstrap.gleam` - `exprs_to_stmts()`
- `src/tao/desugar.gleam` - `desugar_let()` (should already work)

---

## Notes

The grammar library's `opt()` behavior is the root cause of the complexity. A cleaner design might:
1. Use explicit `None` markers for optional values
2. Or use separate rules for `Let` and `LetMut`, `LetTyped` and `LetMutTyped`

But for now, handling variable-length sequences is the pragmatic solution.
