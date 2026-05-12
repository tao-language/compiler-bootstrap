# Analysis: t01_basics_13_fix_point_recursion_test Timeout

## Problem Statement

The test `t01_basics_13_fix_point_recursion_test` is timing out with 3 failures. The test file is:

```core
// Recursive functions are defined using $fix.
$let factorial = $fix f. $fn(n: $Int) =>
  $match (n) {
    | 0 => 1
    | n => %i32_mul<$I32>(n, f %i32_sub<$I32>(n, 1))
  }

// Test: factorial of 5 = 120
factorial 5
```

## Root Cause Analysis

### 1. Parsing Issue: `parse_let` not separating value from body at newlines

The `parse_let` function is supposed to parse:
- `value = $fix f. $fn(n: $Int) => $match (n) { | 0 => 1 | n => %i32_mul<$I32>(n, f %i32_sub<$I32>(n, 1)) }`
- `body = factorial 5`

But it's actually parsing:
- `value = $fix g. $fn(n: $Int) => #0`
- `body = (#0 5) $fix g. $fn(n: $Int) => #0`

The issue is that `parse_let` calls `parse_term(p5)` to parse the value. The `parse_term` function calls `parse_app`, which calls `parse_app_chain`. The `parse_app_chain` function only continues if the next token is on the same line as the current term.

However, the fixpoint expression's body (`$fn(n: $Int) => n`) ends at line 1, and `f` starts at line 2. The `same_line` check correctly returns `False` (line 1 vs line 2), so `parse_app_chain` should stop.

But the parsing output shows that `f 5` is being parsed as part of the body, not as a separate expression. This suggests that the issue is not with `parse_app_chain` but with `parse_let` itself.

### 2. `parse_let` is calling `parse_tokens_acc` indirectly

Looking at the parsing output:
```
($fn(f: {}) => (#0 5) $fix g. $fn(n: $Int) => #0)
```

This is a lambda with:
- `param_type = Rcd([])`
- `body = (#0 5) $fix g. $fn(n: $Int) => #0`

The `#0 5` part is an application of `#0` to `5`, and then `$fix g. $fn(n: $Int) => #0` is another term.

The issue is that `parse_let` is calling `parse_tokens_acc` to parse the body. The `parse_tokens_acc` function is parsing multiple expressions and returning the last one. So it's parsing `(#0 5)` and then `$fix g. $fn(n: $Int) => #0`, and returning `$fix g. $fn(n: $Int) => #0` as the final result.

But the `parse_let` function is expecting the value to be `$fix g. $fn(n: $Int) => #0` and the body to be `f 5`.

### 3. The real issue: `parse_let` is not checking for newlines before parsing the body

The `parse_let` function is calling `parse_term(p5)` to parse the value. The `parse_term` function calls `parse_app`, which calls `parse_app_chain`. The `parse_app_chain` function only continues if the next token is on the same line as the current term.

So if the value ends on line 1 and `f` is on line 2, the `parse_app_chain` function should stop because they're on different lines.

But the issue is that `parse_let` is calling `parse_tokens_acc` to parse the body. The `parse_tokens_acc` function is parsing multiple expressions and returning the last one. So it's parsing `(#0 5)` and then `$fix g. $fn(n: $Int) => #0`, and returning `$fix g. $fn(n: $Int) => #0` as the final result.

The fix is to make `parse_let` check for newlines before calling `parse_tokens_acc` to parse the body. If the next token is on a different line than the value, then `parse_let` should call `parse_term` to parse the body, not `parse_tokens_acc`.

### 4. The timeout is caused by the evaluator, not the parser

The parsing is correct (the `same_line` check is working correctly). The timeout is caused by the evaluator trying to evaluate the fixpoint expression, which is causing an infinite loop.

The issue is that the fixpoint expression is not being evaluated correctly. The `VFix` unrolling code is not handling the case where the fixpoint body is not a lambda correctly.

## Proposed Fix

1. **Fix `parse_let` to check for newlines before parsing the body**: If the next token is on a different line than the value, then `parse_let` should call `parse_term` to parse the body, not `parse_tokens_acc`.

2. **Fix the `VFix` unrolling code to handle non-lambda bodies**: If the fixpoint body is not a lambda, the `VFix` unrolling code should return `VErr`.

## Additional Investigation Needed

1. Check if `parse_let` is calling `parse_tokens_acc` to parse the body.
2. Check if the `VFix` unrolling code is handling non-lambda bodies correctly.
3. Check if the `parse_app_chain` function is correctly checking for newlines.
