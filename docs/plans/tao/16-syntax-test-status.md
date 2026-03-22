# Tao Syntax Test Status

> **Date**: March 15, 2026
> **Status**: 🟢 Error Reporting Fixed

---

## Summary

- **Total Tests**: 504
- **Passing**: 481
- **Failing**: 23

---

## ✅ Fixed: Error Reporting

The grammar now properly reports errors for:
1. **Unconsumed tokens** - If the parser successfully parses but leaves tokens unconsumed, an error is reported
2. **Unknown tokens** - Tokens that don't match any grammar rule produce errors
3. **Missing tokens** - Expected tokens that aren't found produce errors

### Example: Before vs After

**Before (silent failure)**:
```
Input:  1 @ 2
Output: 1 (no error - @ silently ignored)
```

**After (error reported)**:
```
Input:  1 @ 2
Output: error[E0001]: Syntax error in unexpected token after successful parse
        = note: Expected: end of input
        = note: Got: @
```

---

## Passing Tests ✅

### Success Cases (All Passing)
- Basic expressions (numbers, variables)
- Let bindings (simple, mut, type annotations)
- Module parsing
- Round-trip tests (for supported features)
- Formatter tests

### Error Detection (Working)
- `assert_has_error()` confirms errors are produced for invalid syntax
- Error messages include source location and unexpected token

---

## Failing Tests ❌ (23 total)

### Category 1: Core Language Examples (6 failures)

These use the core language grammar (`.core.tao` files), which has different syntax:
- Function application: `k(10)(20)` - `(` not in core grammar tokens
- Type arrows: `->` not properly handled
- These need core grammar updates

### Category 2: Tao Grammar Incomplete (17 failures)

The Tao grammar is missing features:
- **Operators**: Defined in grammar but not used in `Expr` rule
- **Blocks**: `{ ... }` not implemented
- **Functions**: `fn` definitions not fully implemented
- **Pattern matching**: `match { ... }` not implemented
- **Control flow**: `if`, `while`, `for` not implemented

These are **grammar implementation issues**, not error reporting issues. The error reporting is working correctly - it's catching that the grammar doesn't support these features.

---

## Key Changes Made

### 1. Grammar Library Fix (`src/syntax/grammar.gleam`)

Modified the `parse()` function to check for unconsumed tokens:

```gleam
case parse_rule(grammar, rule, tokens, 0) {
  Ok(#(ast, consumed_pos)) -> {
    // Check if there are unconsumed tokens
    case get_token(tokens, consumed_pos) {
      Ok(unexpected_token) => {
        // Error: remaining tokens after successful parse
        let error = ParseError(...)
        ParseResult(ast: error_ast, errors: [error])
      }
      Error(_) => ParseResult(ast, [])  // All consumed
    }
  }
  Error(e) => ParseResult(ast: error_ast, errors: [e])
}
```

### 2. Tao Grammar Fix (`src/tao/syntax.gleam`)

- Added `"Equal"` to tokens list
- Changed `token_pattern("=")` to `token_pattern("Equal")` in Let rule

---

## Next Steps

### High Priority: Complete Tao Grammar

1. **Add operator handling to Expr rule**
   - Use `left_assoc_rule` like the calc example
   - Connect defined operators to expression parsing

2. **Implement missing features**
   - Blocks: `{ stmts }`
   - Functions: `fn name(params) -> body`
   - Pattern matching: `match expr { cases }`
   - Control flow: `if`, `while`, `for`

### Medium Priority: Fix Core Grammar

1. Add function application tokens
2. Fix arrow handling
3. Update core examples

### Low Priority: Improve Error Messages

1. More specific error messages (not just "unexpected token")
2. Error recovery (skip to sync points like `;`, `}`, `,`)
3. Multiple error reporting (don't stop at first error)

---

## Notes

- **Error reporting is now working correctly** - the remaining failures are due to incomplete grammar features
- Tests document expected behavior - they will pass once grammar features are implemented
- The fix prevents silent failures, making debugging much easier
