# Tao Syntax Test Status

> **Date**: March 15, 2026
> **Status**: 🟡 Partially Complete

---

## Summary

- **Total Tests**: 504
- **Passing**: 468
- **Failing**: 36

---

## Passing Tests ✅

### Success Cases (All Passing)
- Basic expressions (numbers, variables, operators)
- Operator precedence
- Let bindings (simple, mut, type annotations)
- Module parsing
- Round-trip tests
- Formatter tests

### Error Detection (Basic)
- `assert_has_error()` helper confirms errors are produced for invalid syntax

---

## Failing Tests ❌

### Error Reporting Tests (36 failing)

The following tests fail because the grammar doesn't properly report errors for unknown/invalid tokens:

1. **Missing Tokens**
   - `parse_error_missing_closing_paren_test()` - Parser doesn't report missing `)`
   - `parse_error_missing_equals_test()` - Parser doesn't report missing `=`
   - `parse_error_missing_type_colon_test()` - Parser doesn't report missing `:`

2. **Invalid Tokens**
   - `parse_error_unknown_operator_test()` - Parser silently ignores `@` operator
   - `parse_error_double_operator_test()` - Parser silently ignores `++` operator
   - `parse_error_missing_operand_test()` - Parser doesn't report missing operand

### Root Cause

The grammar library uses `alt()` to try different alternatives. When an unknown token is encountered:
- The grammar doesn't fail - it returns the last successful parse
- For `1 @ 2`, it parses `1` and silently ignores `@ 2`
- No error is added to the error list

This is a **known limitation** of the current grammar implementation.

---

## Known Issues

### 1. Silent Token Skipping

**Issue**: Unknown tokens are silently skipped instead of producing errors.

**Example**:
```
Input:  1 @ 2
Output: 1 (no error)
```

**Expected**:
```
Input:  1 @ 2
Output: Error: unexpected '@', expected operator
```

**Fix Required**: Update grammar to use error-producing rules for unknown tokens.

### 2. Type Inference Issues in Tests

**Issue**: Gleam's type inference causes issues when trying to access `ParseError` fields in test functions.

**Workaround**: Use `assert_has_error()` helper that only checks for error presence, not error details.

**Example**:
```gleam
// This doesn't compile due to type inference issues:
pub fn test() {
  let result = parse("1 @ 2")
  case list.first(result.errors) {
    Some(error) -> error.got |> should.equal("@")  // Type error!
    None -> panic as "Expected error"
  }
}

// Workaround - just check for error presence:
pub fn test() {
  assert_has_error("1 @ 2")
}
```

---

## Next Steps

### Phase 1: Fix Grammar Error Reporting (High Priority)

1. **Add error-producing rules** for unknown tokens
   - When lexer produces an error token, grammar should fail
   - Add `unexpected_token()` rule that produces `ParseError`

2. **Update operator parsing** to report unknown operators
   - Instead of silently skipping, produce error for unknown operator tokens

3. **Add tests** for error reporting after fix

### Phase 2: Improve Test Helpers (Medium Priority)

1. **Fix type inference issues** in test helpers
   - Use separate module for helper functions
   - Add explicit type annotations

2. **Add detailed error assertions**
   - `assert_error_contains(expected, got)`
   - `assert_error_span(error, line, column)`

### Phase 3: Add More Error Cases (Low Priority)

1. **Add tests for**:
   - Type errors
   - Name resolution errors
   - Import errors

2. **Add CLI integration tests**:
   - Verify error output format
   - Verify exit codes

---

## Test Coverage

| Category | Tests | Passing | Failing | Notes |
|----------|-------|---------|---------|-------|
| Success Cases | 80+ | ✅ All | - | Basic parsing works |
| Operator Precedence | 10+ | ✅ All | - | Precedence correct |
| Let Bindings | 10+ | ✅ All | - | Parsing works |
| Round-Trip | 20+ | ✅ All | - | Format matches source |
| Error Detection | 10 | ❌ 0 | 10 | Grammar doesn't report errors |
| Error Recovery | 5 | ⏳ TBD | - | Not yet implemented |

---

## Notes

- The grammar library needs updates to properly report errors
- Tests are structured to be enabled once grammar is fixed
- Current tests document expected behavior for future implementation
