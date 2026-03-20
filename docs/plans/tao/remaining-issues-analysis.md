# Tao Compiler Remaining Issues Analysis

## Overview

This document provides a comprehensive analysis of the remaining issues in the Tao compiler and a detailed plan to fix them.

**Current Test Status:** 504 passing, 5 failures

## Issue 1: Constructor Type Inference

### Problem

When using polymorphic constructors like `Some(42)`, the type parameter is not being inferred correctly. The expected type is `Option(I32)` but we get `Option(Type(0))`.

### Root Cause Analysis

The issue is in how constructor type parameters are handled during type inference. Let me trace through what happens:

1. **Constructor Definition** (`prelude_ctrs`):
   ```gleam
   #("Some", CtrDef(["a"], Var(0, no_span), Typ(0, no_span)))
   ```
   - Parameter "a" with type `Var(0)` (references the parameter itself)
   - Return type `Typ(0)` (Type universe 0)

2. **check_ctr_def** creates holes for parameters:
   ```gleam
   let s = State(..s, ctx: [#(name, #(hole, hole)), ..s.ctx])
   ```
   - Creates hole for both value and type of parameter

3. **infer** for constructor application:
   ```gleam
   let #(params, ctr_arg_ty, ctr_ret_ty, s) = check_ctr_def(s, ctr)
   let #(_, arg_ty, s) = infer(s, arg)  // arg_ty = I32T
   let #(_, s) = check_type(s, arg_ty, ctr_arg_ty, ...)  // Unify I32T with Var(0)
   ```

4. **The Problem**: `ctr_arg_ty` is `Var(0)` which refers to the parameter in the context. When we unify `I32T` with `Var(0)`, we're trying to unify with a variable reference, not the hole itself.

### Solution

The constructor definition needs to be changed so that:
- `arg_ty` directly contains the hole (not a reference to it)
- `ret_ty` should be a proper type application like `App(Option, a)`

**Fix:** Change prelude constructor definitions to use proper type structure:

```gleam
#("Some", CtrDef(["a"], Hole(0, span), App(Var("Option", span), Hole(0, span), span), span))
```

But this requires the core language to support `Hole` in constructor definitions and proper type application.

**Alternative Fix:** Modify `check_ctr_def` to substitute the parameter holes into arg_ty and ret_ty after creating them.

## Issue 2: Recursive Function Parsing

### Problem

Recursive function definitions fail to parse:
```tao
fn factorial(n: I32) -> I32 {
  match n {
    | 0 -> 1
    | _ -> n * factorial(n - 1)
  }
}
```

Error: "Syntax error in unexpected token after successful parse"

### Root Cause Analysis

Looking at the grammar in `src/tao/syntax.gleam`:

1. **Program rule** uses `many(seq([ref("Stmt"), opt(token_pattern("Semi"))]))`
2. **Block rule** uses `many(ref("Stmt"))`
3. **Fn rule** expects a `Block` as body

The issue is that when parsing a function body, the parser treats the opening `{` as starting a new program scope, and then encounters statements that look like top-level statements.

### Solution

The grammar needs to be fixed to properly handle nested blocks. The `Block` rule should consume statements until the matching `}` without treating them as a separate program.

**Fix:** Modify the `Block` rule to properly handle statement parsing within braces, ensuring statements inside blocks are parsed as block statements, not as a new program.

## Issue 3: Higher-Order Function Parsing

### Problem

Lambda expressions in certain contexts fail to parse correctly.

### Root Cause Analysis

The grammar for lambdas may conflict with other expression forms. Need to check:
- Lambda rule in grammar
- How lambdas interact with application
- Operator precedence

### Solution

Review and fix the lambda grammar rule to ensure proper precedence and avoid conflicts.

## Issue 4: Exhaustiveness Test Failure

### Problem

`check_exhaustiveness_rcd_test` expects `MatchRedundantCase` but gets `[]`.

### Root Cause Analysis

The test creates a match with:
```gleam
[case_(prcd([]), i32(1, s0), s1), case_(pany, i32(2, s0), s2)]
```

A record pattern followed by wildcard. The wildcard makes the match exhaustive, but the record pattern should not be marked as redundant (it's more specific than wildcard).

### Solution

The redundant case detection is too aggressive. A pattern is only redundant if a *previous* pattern already covers all cases it would match. A specific pattern before a wildcard is not redundant.

**Fix:** Modify `is_pattern_covered_by` to only return true if the covering pattern is strictly more general AND appears earlier in the list.

## Issue 5: Selective Import Example

### Problem

`examples/tao/programs/07-modules/selective_import.tao` fails with type errors.

### Root Cause Analysis

The file imports `not` from `prelude/bool`, but `not` is a builtin function, not a constructor. The import desugaring may not be handling builtin functions correctly.

### Solution

Ensure builtin functions are available by name in the FFI environment and don't need explicit import bindings.

## Implementation Plan

### Phase 1: Fix Constructor Type Inference (Highest Priority)

1. Modify `check_ctr_def` to properly substitute parameter holes into arg_ty and ret_ty
2. Ensure unification solves the holes correctly
3. Verify ctr_solve_params returns solved types
4. Test with `Some(42)` example

### Phase 2: Fix Recursive Function Parsing

1. Review Block grammar rule
2. Fix statement parsing within blocks
3. Test with recursive function examples

### Phase 3: Fix Higher-Order Function Parsing

1. Review lambda grammar rule
2. Fix precedence conflicts
3. Test with lambda examples

### Phase 4: Fix Remaining Test Failures

1. Fix exhaustiveness test
2. Fix selective import example
3. Run full test suite

## Timeline

- Phase 1: 2-3 hours
- Phase 2: 1-2 hours
- Phase 3: 1-2 hours
- Phase 4: 1 hour

Total: 5-8 hours
