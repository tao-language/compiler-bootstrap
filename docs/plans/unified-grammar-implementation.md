# Unified Grammar System - Implementation Plan

> **Status**: ✅ Phase 1-4 complete, Phase 5 deferred
> **Date**: March 2025

---

## Current Status

### ✅ Working

- Lexer tokenizes numbers, identifiers, operators, parentheses, strings, comments
- Grammar DSL with declarative builder pattern
- Parser handles all patterns (Token, Keyword, Op, Ref, Seq, Choice, Opt, Many, Sep1, Parens)
- **Left-associative operator parsing** - Correctly handles multiple operators at same precedence
- **Operator precedence** - Higher precedence operators bind tighter
- **Parenthesized expressions** - Correctly overrides precedence
- Formatter document algebra (rendering works)
- **222 tests passing**

### ⏳ Needs Work

1. **Automatic formatter** - Returns `<ast>` placeholder, needs deconstructors
2. **Error handling** - Panics on parse failure instead of returning errors

---

## Implementation Plan: Get Calc Example Fully Working

### Phase 1: Fix Left-Associative Operator Parsing ✅

**Problem**: The `Many` combinator returns a flat `List(Value(a))`, but for left-associative operators we need to fold them correctly.

**Solution implemented**:
1. Changed `Many` to wrap each matched sequence in `ListValue`
2. Updated `fold_operators_multi` to handle the nested structure
3. Changed `left_assoc` to create a single alternative with `Choice` for multiple operators at same precedence

**Files modified**:
- `src/syntax/grammar.gleam` - `parse_many`, `create_operator_pattern`, `fold_operators_multi`

**Tests passing**:
- ✅ `parse_left_assoc_test()` - `1 + 2 + 3` = `Add(Add(1, 2), 3)`
- ✅ `parse_mul_div_mix_test()` - `12 / 3 * 2` = `Mul(Div(12, 3), 2)`

### Phase 2: Fix Parenthesized Expressions ✅

**Problem**: Parenthesized expressions weren't parsing correctly.

**Solution implemented**:
1. Changed `grammar.parenthesized()` to return `Parens` pattern instead of `Seq`
2. `parse_parens` wraps result in `ParensValue` for special handling

**Files modified**:
- `src/syntax/grammar.gleam` - `parenthesized()` function

**Tests passing**:
- ✅ `parse_parens_number_test()` - `(42)` = `Int(42)`
- ✅ `parse_parens_add_test()` - `(1 + 2)` = `Add(1, 2)`
- ✅ `parse_parens_override_precedence_test()` - `(1 + 2) * 3` = `Mul(Add(1, 2), 3)`
- ✅ `parse_parens_nested_test()` - `((1 + 2) * 3)` = `Mul(Add(1, 2), 3)`

### Phase 3: Fix Operator Precedence ✅

**Problem**: Multiple operators at same precedence level (e.g., `*` and `/`) weren't handled correctly.

**Solution implemented**:
1. Changed `left_assoc` to create a single alternative with `Choice` of operators
2. Added `fold_operators_multi` that looks up the correct operator by token value

**Files modified**:
- `src/syntax/grammar.gleam` - `left_assoc`, `create_operator_pattern`, `fold_operators_multi`

**Tests passing**:
- ✅ `parse_precedence_test()` - `1 + 2 * 3` = `Add(1, Mul(2, 3))`
- ✅ `parse_complex_precedence_test()` - `2 * 3 + 4 * 5` = `Add(Mul(2, 3), Mul(4, 5))`
- ✅ `parse_all_operators_test()` - `1 + 2 * 3 - 4 / 2` = `Sub(Add(1, Mul(2, 3)), Div(4, 2))`

### Phase 4: Add Comprehensive Tests ✅

**Tests added**:
- Number parsing (single digit, multi-digit, zero)
- Addition (simple, multiple, four operands)
- Subtraction (simple, multiple)
- Multiplication (simple, multiple)
- Division (simple)
- Precedence (mul before add, mul before sub, complex)
- Parentheses (number, add, override precedence, nested, complex, deeply nested)
- Mixed operators (add/sub mix, mul/div mix, all operators)
- Formatting (int, add, mul) - currently return `<ast>` placeholder

**Test results**: 222 passed, no failures

### Phase 5: Error Handling ⏳ DEFERRED

**Problem**: Parser panics with "Parse failed" on invalid input.

**Current behavior**:
```gleam
parse("abc")  // Panics
```

**Expected behavior**:
```gleam
parse("abc")  // Returns ParseResult with errors list
```

**Status**: Tests commented out, to be implemented in future iteration.

**Files to modify**:
- `src/syntax/grammar.gleam` - `parse`, `parse_rule`, `try_alternatives`

---

## Test Results

```
222 passed, no failures
```

All core language tests pass, plus 26 new syntax tests for the calc example.

---

## Implementation Order (Completed)

1. ✅ **Phase 1** - Fix left-associative parsing
2. ✅ **Phase 2** - Fix parenthesized expressions
3. ✅ **Phase 3** - Fix operator precedence for multiple operators at same level
4. ✅ **Phase 4** - Add comprehensive tests
5. ⏳ **Phase 5** - Improve error handling (deferred)

---

## Next Steps

1. **Implement automatic formatter** - Add deconstructors to extract operands from AST for formatting
2. **Improve error handling** - Return descriptive errors instead of panicking
3. **Add round-trip tests** - Verify parse → format → parse produces same output
4. **Migrate core.gleam** - Use new grammar system for core language parsing
5. **Add more examples** - Lambda calculus, let-language

---

## Notes

- Keep changes minimal and incremental
- Test after each phase
- Document any design decisions in comments
- Keep the API simple and consistent
