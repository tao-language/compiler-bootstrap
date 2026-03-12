# Testing Guide

> **Philosophy**: Tests are documentation. They should be useful to read and learn from.

---

## Important: Read This First

For Gleam to recognize tests:
- ⚠️ The filename **must** end with `_test.gleam`.
- ⚠️ The test function **must** be a `pub fn` and end with `_test()`.

**Before modifying tests**, read **[Lessons Learned](../docs/lessons-learned.md)**.

Key insights for testing:
- ⚠️ **Test variables may be used in pattern matching** - Don't prefix with `_` without reading full test
- ⚠️ **One assertion per test** - Makes failures easier to debug
- ⚠️ **Check structural equality** - Not just success/failure
- ⚠️ **Test error cases** - Not just happy paths


---

## Table of Contents

1. [Test Philosophy](#test-philosophy)
2. [How Tests Work in Gleam](#how-tests-work-in-gleam)
3. [Writing Good Tests](#writing-good-tests)
4. [Test Organization](#test-organization)
5. [Debugging Failing Tests](#debugging-failing-tests)
6. [Getting Good Coverage](#getting-good-coverage)
7. [Tips and Tricks](#tips-and-tricks)
8. [Guide for AI Assistants](#guide-for-ai-assistants)

---

## Test Philosophy

### Tests as Documentation

**Every test should teach something.** When someone reads your tests, they should learn:

1. **How the API works** - Clear examples of function usage
2. **What to expect** - Exact return values, not just "no error"
3. **Edge cases** - How the API handles unusual inputs
4. **Error cases** - What errors look like and when they occur

### Example: Bad vs Good Test

**❌ Bad Test** (not useful as documentation):
```gleam
pub fn parse_test() {
  let result = parse("1 + 2")
  result |> should.be_ok
}
```

This tells us nothing about:
- What the parsed AST looks like
- Whether the structure is correct
- How operators are associated

**✅ Good Test** (useful as documentation):
```gleam
pub fn parse_add_test() {
  let result = parse("1 + 2")
  result.ast |> should.equal(Add(Int(1), Int(2)))
  result.errors |> should.equal([])
}
```

This teaches:
- `parse()` returns a result with an `ast` field
- `"1 + 2"` parses to `Add(Int(1), Int(2))`
- The exact structure of the AST
- There were no syntax errors when parsing this

### Strict Structural Equality

**Always check structural equality**, not just success/failure:

```gleam
// ✅ Good: Check exact structure
result.ast |> should.equal(Add(Int(1), Int(2)))

// ❌ Bad: Just check for success
result |> should.be_ok

// ❌ Bad: Check only part of the structure
case result.ast {
  Add(_, _) -> True
  _ -> False
} |> should.be_true
```

**Why?**
1. **Catches regressions** - If the AST structure changes, tests fail
2. **Documents behavior** - Future readers see exactly what to expect
3. **Finds bugs early** - Wrong structure is caught immediately

### Test Categories

1. **Unit Tests** - Test individual functions in isolation
2. **Integration Tests** - Test multiple functions working together
3. **Round-Trip Tests** - Verify symmetry (parse → format → parse)
4. **Error Tests** - Verify error handling and messages
5. **Property Tests** - Verify general properties (future enhancement)

---

## How Tests Work in Gleam

### Test Framework

This project uses **gleeunit**, a simple test framework:

```gleam
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}
```

### Test Function Naming

Tests are functions that:
- End with `_test` suffix
- Take no arguments
- Return `Nil`
- Use `should` assertions

```gleam
pub fn parse_number_test() {
  let result = parse("42")
  result.ast |> should.equal(Int(42))
}

pub fn parse_add_test() {
  let result = parse("1 + 2")
  result.ast |> should.equal(Add(Int(1), Int(2)))
}
```

### Assertions

Use `gleeunit/should` for assertions:

```gleam
import gleeunit/should

// Equality
value |> should.equal(expected)

// Boolean checks
value |> should.be_true
value |> should.be_false

// Option checks
value |> should.be_some
value |> should.be_none

// Result checks
result |> should.be_ok
result |> should.be_error

// With custom message
value |> should.equal(expected, message: "custom message")
```

### Running Tests

```bash
# Run all tests
gleam test

# Run tests with output
gleam test --verbose
```

---

## Writing Good Tests

### 1. Test Names Should Be Descriptive

```gleam
// ✅ Good: Clear what's being tested
pub fn parse_number_single_digit_test()
pub fn parse_number_multi_digit_test()
pub fn parse_add_left_associative_test()

// ❌ Bad: Unclear what's being tested
pub fn test1()
pub fn number_test()
pub fn parse_test()
```

### 2. Arrange-Act-Assert Pattern

Structure tests clearly:

```gleam
pub fn parse_add_with_parens_test() {
  // Arrange
  let source = "(1 + 2) * 3"

  // Act
  let result = parse(source)

  // Assert
  result.ast |> should.equal(Mul(Add(Int(1), Int(2)), Int(3)))
}
```

### 3. Test One Thing Per Test

```gleam
// ✅ Good: One assertion per test
pub fn parse_add_test() {
  parse("1 + 2").ast |> should.equal(Add(Int(1), Int(2)))
}

pub fn parse_sub_test() {
  parse("1 - 2").ast |> should.equal(Sub(Int(1), Int(2)))
}

// ❌ Bad: Multiple assertions in one test
pub fn parse_operators_test() {
  parse("1 + 2").ast |> should.equal(Add(Int(1), Int(2)))
  parse("1 - 2").ast |> should.equal(Sub(Int(1), Int(2)))
  parse("1 * 2").ast |> should.equal(Mul(Int(1), Int(2)))
}
```

**Why?** When a test fails, you know exactly what broke.

### 4. Test Error Cases

Don't just test success cases:

```gleam
pub fn parse_invalid_syntax_test() {
  let result = parse("1 +")
  result.errors |> should.not.be_empty
}

pub fn parse_unknown_token_test() {
  let result = parse("@#$")
  result.errors |> should.not.be_empty
}
```

### 5. Use Helper Functions for Common Patterns

```gleam
// Helper function
fn parse_ok(source: String) -> Expr {
  let result = parse(source)
  case result {
    ParseResult(ast, []) -> ast
    _ -> panic as "Parse failed: " <> inspect(result.errors)
  }
}

// Test using helper
pub fn parse_nested_add_test() {
  parse_ok("1 + 2 + 3")
  |> should.equal(Add(Add(Int(1), Int(2)), Int(3)))
}
```

### 6. Include Comments for Complex Tests

```gleam
pub fn parse_precedence_test() {
  // 1 + 2 * 3 should parse as 1 + (2 * 3), not (1 + 2) * 3
  // because * has higher precedence than +
  parse_ok("1 + 2 * 3")
  |> should.equal(Add(Int(1), Mul(Int(2), Int(3))))
}
```

---

## Test Organization

### File Structure

Tests should follow the same directory and file structure as the source code, but with a `_test` suffix. For example:

- **Source file**: `src/syntax/grammar.gleam`
- **Test file**: `test/syntax/grammar_test.gleam`

### Group Related Tests

Keep related tests together:

```gleam
// parser_test.gleam

// Number parsing tests
pub fn parse_number_single_digit_test() { ... }
pub fn parse_number_multi_digit_test() { ... }
pub fn parse_number_zero_test() { ... }

// Addition tests
pub fn parse_add_simple_test() { ... }
pub fn parse_add_multiple_test() { ... }
pub fn parse_add_left_associative_test() { ... }

// Precedence tests
pub fn parse_precedence_mul_before_add_test() { ... }
pub fn parse_precedence_parens_test() { ... }
```

### Use Test Suites for Large Projects

For larger projects, organize into modules:

```gleam
// test/parser/numbers_test.gleam
pub fn single_digit_test() { ... }
pub fn multi_digit_test() { ... }

// test/parser/operators_test.gleam
pub fn add_test() { ... }
pub fn mul_test() { ... }
```

---

## Debugging Failing Tests

### Read the Error Message

Gleeunit shows:
- Which test failed
- Expected value
- Actual value
- Line number

```
✗ parse_add_test failed
  Expected: Add(Int(1), Int(2))
  Actual:   Add(Int(1), Int(3))
  at test/parser_test.gleam:15
```

### Add Debug Output

Use `io.println` for debugging:

```gleam
import gleam/io

pub fn parse_debug_test() {
  let result = parse("1 + 2")
  io.println("Result: " <> inspect(result))
  result.ast |> should.equal(Add(Int(1), Int(2)))
}
```

### Use `inspect` for Complex Values

```gleam
import gleam/dynamic

pub fn parse_complex_test() {
  let result = parse("1 + 2 * 3")
  // Print the AST structure for debugging
  io.println("AST: " <> inspect(result.ast))
  result.ast |> should.equal(Add(Int(1), Mul(Int(2), Int(3))))
}
```

### Isolate the Failure

If a test fails, create a minimal reproduction:

```gleam
// Minimal test to isolate the issue
pub fn minimal_failure_test() {
  parse("1 + 2").ast |> should.equal(Add(Int(1), Int(2)))
}
```

### Check Prerequisites

Make sure your test setup is correct:

```gleam
pub fn parse_test() {
  // Check that the grammar is defined correctly
  let grammar = calc_grammar()
  io.println("Grammar: " <> inspect(grammar))

  let result = parse("1 + 2")
  result.ast |> should.equal(Add(Int(1), Int(2)))
}
```

---

## Getting Good Coverage

### Cover All Code Paths

For each function, test:

1. **Normal case** - Typical successful usage
2. **Edge cases** - Boundary conditions
3. **Error cases** - Invalid inputs

```gleam
// Normal case
pub fn parse_number_normal_test() {
  parse_ok("42") |> should.equal(Int(42))
}

// Edge case: zero
pub fn parse_number_zero_test() {
  parse_ok("0") |> should.equal(Int(0))
}

// Edge case: large number
pub fn parse_number_large_test() {
  parse_ok("999999") |> should.equal(Int(999999))
}

// Error case: not a number
pub fn parse_number_invalid_test() {
  let result = parse("abc")
  result.errors |> should.not.be_empty
}
```

### Test Boundary Conditions

```gleam
// Single digit
pub fn parse_single_digit_test() {
  parse_ok("1") |> should.equal(Int(1))
}

// Multi-digit
pub fn parse_multi_digit_test() {
  parse_ok("123") |> should.equal(Int(123))
}

// Maximum/minimum values (if applicable)
pub fn parse_max_int_test() {
  parse_ok("9223372036854775807")
  |> should.equal(Int(9223372036854775807))
}
```

### Test Combinations

For functions that interact, test combinations:

```gleam
// Individual operators
pub fn parse_add_test() { ... }
pub fn parse_mul_test() { ... }

// Mixed operators
pub fn parse_add_mul_test() {
  parse_ok("1 + 2 * 3")
  |> should.equal(Add(Int(1), Mul(Int(2), Int(3))))
}

// Multiple mixed operators
pub fn parse_all_operators_test() {
  parse_ok("1 + 2 * 3 - 4 / 2")
  |> should.equal(Sub(Add(Int(1), Mul(Int(2), Int(3))), Div(Int(4), Int(2))))
}
```

### Round-Trip Tests

For parse/format pairs, test round-trips:

```gleam
pub fn roundtrip_add_test() {
  let source = "1 + 2"
  let result = parse(source)
  let formatted = format(result.ast)
  let result2 = parse(formatted)

  // Both should produce the same AST
  result.ast |> should.equal(result2.ast)
}

pub fn roundtrip_precedence_test() {
  let source = "1 + 2 * 3"
  let result = parse(source)
  let formatted = format(result.ast)

  // Formatted should be identical (no extra parens)
  formatted |> should.equal(source)

  // Re-parsing should produce same AST
  parse(formatted).ast |> should.equal(result.ast)
}
```

### Measure Coverage

Use Gleam's coverage tools (if available):

```bash
# Run tests with coverage
gleam test --coverage

# View coverage report
# (Check output for uncovered lines)
```

Focus on:
- **Branch coverage** - All `case` branches tested
- **Line coverage** - All lines executed
- **Path coverage** - All execution paths tested

---

## Tips and Tricks

### 1. Start Small

Begin with the simplest test:

```gleam
// Start with the simplest case
pub fn parse_number_test() {
  parse_ok("42") |> should.equal(Int(42))
}

// Then add complexity
pub fn parse_add_test() {
  parse_ok("1 + 2") |> should.equal(Add(Int(1), Int(2)))
}

// Then test edge cases
pub fn parse_left_associative_test() {
  parse_ok("1 + 2 + 3")
  |> should.equal(Add(Add(Int(1), Int(2)), Int(3)))
}
```

### 2. Run Tests Frequently

Run tests after every small change:

```bash
# Terminal 1: Watch mode (if available)
fswatch -or test src | xargs -n1 -I{} gleam test

# Terminal 2: Make changes and save
# Tests run automatically
```

### 3. Use `panic` for Test Helpers

If a helper function fails, it's a test bug, not a test failure:

```gleam
fn parse_ok(source: String) -> Expr {
  let result = parse(source)
  case result {
    ParseResult(ast, []) -> ast
    _ -> panic as "Test bug: parse failed unexpectedly: " <> inspect(result.errors)
  }
}
```

### 4. Group Tests with Comments

```gleam
// ============================================================================
// NUMBER PARSING TESTS
// ============================================================================

pub fn parse_number_single_digit_test() { ... }
pub fn parse_number_multi_digit_test() { ... }

// ============================================================================
// OPERATOR PARSING TESTS
// ============================================================================

pub fn parse_add_test() { ... }
pub fn parse_mul_test() { ... }
```

### 5. Test API Evolution

When changing the API, update tests to reflect the new API:

```gleam
// Old API
pub fn parse_old_test() {
  parse("1 + 2") |> should.equal(Ok(Add(Int(1), Int(2))))
}

// New API (updated)
pub fn parse_new_test() {
  parse("1 + 2").ast |> should.equal(Add(Int(1), Int(2)))
}
```

### 6. Keep Tests Fast

Avoid slow operations in tests:

```gleam
// ✅ Good: Fast test
pub fn parse_test() {
  parse("1 + 2").ast |> should.equal(Add(Int(1), Int(2)))
}

// ❌ Bad: Slow test (don't do this)
pub fn parse_slow_test() {
  // Don't read files, make network calls, etc.
  let source = read_file("test/fixtures/large_program.gleam")
  parse(source).ast |> should.equal(...)
}
```

### 7. Use Descriptive Failure Messages

```gleam
// Without message
result.ast |> should.equal(expected)

// With message (for complex tests)
result.ast |> should.equal(
  expected,
  message: "AST should match for source: " <> source
)
```

### 8. Test With Dummy Values First

Sometimes it's hard or tricky to know exactly the output, of a function.
For example, there might be an end-to-end test checking for an error message
in a medium sized piece of code.

Instead of trying to _guess_ the span (location) of where the error happened,
you can use a dummy value like `filename:0:0` which **should** fail,
but the test error message will tell you the actual value that resulted,
like `test.txt:5:3` for example.
Just validate that the value makes sense and looks correct, then you can 
update the test expected result to match.

This way we make sure the spans are collected correctly, and we can catch any
regressions if some code breaks it.

---

## Guide for AI Assistants

### When Writing Tests

Run tests frequently.

1. **Always check structural equality**
   ```gleam
   // ✅ Good
   result.ast |> should.equal(Add(Int(1), Int(2)))

   // ❌ Bad
   result |> should.be_ok
   ```

2. **One assertion per test**
   ```gleam
   // ✅ Good: Separate tests
   pub fn parse_add_test() { ... }
   pub fn parse_sub_test() { ... }

   // ❌ Bad: Multiple assertions
   pub fn parse_operators_test() {
     parse("1 + 2").ast |> should.equal(...)
     parse("1 - 2").ast |> should.equal(...)
   }
   ```

3. **Test error cases**
   ```gleam
   pub fn parse_invalid_test() {
     let result = parse("1 +")
     result.errors |> should.not.be_empty
   }
   ```

4. **Use descriptive names**
   ```gleam
   // ✅ Good
   pub fn parse_add_left_associative_test()

   // ❌ Bad
   pub fn test1()
   ```

5. **Include comments for non-obvious tests**
   ```gleam
   pub fn parse_precedence_test() {
     // * binds tighter than +, so 1 + 2 * 3 = 1 + (2 * 3)
     parse_ok("1 + 2 * 3")
     |> should.equal(Add(Int(1), Mul(Int(2), Int(3))))
   }
   ```

### When Debugging Tests

1. **Read the error message carefully**
   - Expected vs actual
   - Line number
   - Test name

2. **Add debug output if needed**
   ```gleam
   io.println("Result: " <> inspect(result))
   ```

3. **Isolate the failure**
   - Create minimal reproduction
   - Test one thing at a time

4. **Check test setup**
   - Grammar defined correctly?
   - Helper functions working?
   - Imports correct?

### When Refactoring Tests

1. **Keep tests passing**
   - Update tests when API changes
   - Don't break existing tests

2. **Maintain test quality**
   - Keep structural equality checks
   - Keep descriptive names
   - Keep comments for non-obvious tests

3. **Don't remove tests**
   - Even if they seem redundant
   - Multiple tests for the same feature is okay

### Common Mistakes to Avoid

1. **❌ Testing only success**
   ```gleam
   // Missing: error cases
   pub fn parse_test() {
     parse("1 + 2").ast |> should.equal(Add(Int(1), Int(2)))
   }
   ```

2. **❌ Weak assertions**
   ```gleam
   // Not checking structure
   pub fn parse_test() {
     parse("1 + 2") |> should.be_ok
   }
   ```

3. **❌ Multiple assertions**
   ```gleam
   // Hard to debug when fails
   pub fn parse_test() {
     parse("1 + 2").ast |> should.equal(...)
     parse("1 - 2").ast |> should.equal(...)
     parse("1 * 2").ast |> should.equal(...)
   }
   ```

4. **❌ Unclear test names**
   ```gleam
   // What does this test?
   pub fn test1() { ... }
   ```

### Best Practices Summary

| Do | Don't |
|----|-------|
| Check structural equality | Just check for success |
| One assertion per test | Multiple assertions |
| Descriptive test names | Generic names like `test1` |
| Test error cases | Only test success |
| Include comments for complex tests | Assume tests are self-explanatory |
| Use helper functions | Repeat setup code |
| Run tests frequently | Run tests only at the end |
| Start with simple tests | Start with complex tests |

---

## Example Test File

Here's a complete example test file following all best practices:

```gleam
import gleeunit
import gleeunit/should
import syntax/grammar
import examples/calc.{type Expr, Add, Int, Mul, parse, format}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

fn parse_ok(source: String) -> Expr {
  let result = parse(source)
  case result {
    ParseResult(ast, []) -> ast
    _ -> panic as "Parse failed: " <> inspect(result.errors)
  }
}

// ============================================================================
// NUMBER PARSING TESTS
// ============================================================================

pub fn parse_number_single_digit_test() {
  parse_ok("42") |> should.equal(Int(42))
}

pub fn parse_number_multi_digit_test() {
  parse_ok("123") |> should.equal(Int(123))
}

pub fn parse_number_zero_test() {
  parse_ok("0") |> should.equal(Int(0))
}

// ============================================================================
// ADDITION TESTS
// ============================================================================

pub fn parse_add_simple_test() {
  parse_ok("1 + 2") |> should.equal(Add(Int(1), Int(2)))
}

pub fn parse_add_multiple_test() {
  parse_ok("1 + 2 + 3")
  |> should.equal(Add(Add(Int(1), Int(2)), Int(3)))
}

pub fn parse_add_left_associative_test() {
  // 1 + 2 + 3 should parse as (1 + 2) + 3, not 1 + (2 + 3)
  parse_ok("1 + 2 + 3")
  |> should.equal(Add(Add(Int(1), Int(2)), Int(3)))
}

// ============================================================================
// PRECEDENCE TESTS
// ============================================================================

pub fn parse_precedence_mul_before_add_test() {
  // * binds tighter than +, so 1 + 2 * 3 = 1 + (2 * 3)
  parse_ok("1 + 2 * 3")
  |> should.equal(Add(Int(1), Mul(Int(2), Int(3))))
}

pub fn parse_precedence_parens_test() {
  // Parens override precedence: (1 + 2) * 3
  parse_ok("(1 + 2) * 3")
  |> should.equal(Mul(Add(Int(1), Int(2)), Int(3)))
}

// ============================================================================
// FORMAT TESTS
// ============================================================================

pub fn format_add_test() {
  format(Add(Int(1), Int(2))) |> should.equal("1 + 2")
}

pub fn format_precedence_test() {
  // Should not add unnecessary parens
  format(Add(Int(1), Mul(Int(2), Int(3))))
  |> should.equal("1 + 2 * 3")
}

pub fn format_parens_needed_test() {
  // Should add parens when needed
  format(Mul(Add(Int(1), Int(2)), Int(3)))
  |> should.equal("(1 + 2) * 3")
}

// ============================================================================
// ROUND-TRIP TESTS
// ============================================================================

pub fn roundtrip_number_test() {
  let source = "42"
  let ast = parse_ok(source)
  format(ast) |> should.equal(source)
}

pub fn roundtrip_add_test() {
  let source = "1 + 2"
  let ast = parse_ok(source)
  format(ast) |> should.equal(source)
}

pub fn roundtrip_precedence_test() {
  let source = "1 + 2 * 3"
  let ast = parse_ok(source)
  let formatted = format(ast)

  // Formatted should be identical (no extra parens)
  formatted |> should.equal(source)

  // Re-parsing should produce same AST
  parse_ok(formatted) |> should.equal(ast)
}

// ============================================================================
// ERROR TESTS
// ============================================================================

pub fn parse_invalid_syntax_test() {
  let result = parse("1 +")
  result.errors |> should.not.be_empty
}

pub fn parse_unknown_token_test() {
  let result = parse("@#$")
  result.errors |> should.not.be_empty
}

pub fn parse_empty_input_test() {
  let result = parse("")
  result.errors |> should.not.be_empty
}
```

---

## References

- [gleeunit Documentation](https://hexdocs.pm/gleeunit/)
- [Gleam Testing Guide](https://gleam.run/book/tour/testing.html)
- [Should Assertions](https://hexdocs.pm/gleeunit/gleeunit/should.html)
