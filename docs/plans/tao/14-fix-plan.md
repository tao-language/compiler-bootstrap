# Tao Compiler Fix Plan

> **Goal**: Fix remaining Tao compiler issues to achieve 100% test pass rate
> **Status**: ⏳ **In Progress** - Analysis complete, implementation starting
> **Date**: March 18, 2026

---

## Status

### What's Working

- ✅ Function application parsing (fixed grammar left recursion)
- ✅ Fixpoint unfolding (with self-reference detection)
- ✅ Builtin name resolution
- ✅ Basic function evaluation
- ✅ **505 tests passing** (up from 499)

### What's Failing (10 tests)

| Test | Issue | Root Cause |
|------|-------|------------|
| `nested_fn.tao` | Type errors | Nested function scoping |
| `lambda.tao` | Output `?-1` | Lambda evaluation with type annotations |
| `higher_order.tao` | Parse error | Function type parsing in parameters |
| `variable_pattern.tao` | Type errors | Pattern matching evaluation |
| `match_guard.tao` | Type errors (3) | Match guard evaluation |
| `constructor_pattern.tao` | Type errors | Constructor pattern matching |
| `recursive_fn.tao` | Parse error | Recursive function parsing |
| `test_import.tao` | Type errors | Import resolution |
| `selective_import.tao` | Type errors | Selective import resolution |
| `import_example.tao` | Type errors | Import resolution |

### Related

- See **[01-overview.md](./01-overview.md)** for Tao language overview
- See **[12-import-system.md](./12-import-system.md)** for import system specification
- See **[13-stmt-system.md](./13-stmt-system.md)** for Stmt system design

---

## Root Cause Analysis

### Issue 1: Function Type Parsing

**Problem**: Function types like `fn(I32) -> I32` in parameter annotations are not being parsed correctly.

**Example**:
```tao
fn apply(f: fn(I32) -> I32, x: I32) -> I32 {
  f(x)
}
```

**Root Cause**: The grammar's Type rule doesn't handle nested function types correctly. The `fn` keyword in type position conflicts with function definition parsing.

**Location**: `src/tao/syntax.gleam` - Type grammar rule (lines 769-818)

**Fix Required**:
1. Make function type parsing more specific
2. Handle nested parentheses correctly
3. Ensure function types can appear in parameter annotations

---

### Issue 2: Recursive Function Parsing

**Problem**: Recursive functions with pattern matching are not being parsed correctly.

**Example**:
```tao
fn factorial(n: I32) -> I32 {
  match n {
    | 0 -> 1
    | _ -> n * factorial(n - 1)
  }
}
```

**Root Cause**: The grammar doesn't handle `match` expressions in function bodies correctly, or the `match` syntax is not being parsed properly.

**Location**: `src/tao/syntax.gleam` - Match expression parsing

**Fix Required**:
1. Verify match expression grammar
2. Ensure match can appear in function bodies
3. Test recursive calls within match

---

### Issue 3: Pattern Matching Evaluation

**Problem**: Pattern matching produces type errors or incorrect output.

**Examples**:
```tao
-- Variable pattern
match x -> I32 {
  | y -> y
}

-- Constructor pattern
match some_value {
  | Some(x) -> x
  | None -> 0
}

-- Match with guards
match x {
  | n if n > 0 && n < 10 -> "positive small number"
  | _ -> "other"
}
```

**Root Cause**: 
1. Pattern matching desugaring may be incorrect
2. Variable binding in patterns may not be working
3. Match guard evaluation may be broken
4. Constructor pattern matching may not be implemented

**Location**: `src/tao/desugar.gleam` - Match desugaring

**Fix Required**:
1. Review match desugaring logic
2. Verify pattern variable binding
3. Test guard evaluation
4. Check constructor pattern handling

---

### Issue 4: Import Resolution

**Problem**: Imported names are not being resolved correctly during evaluation.

**Examples**:
```tao
import prelude/bool.{True}
True  -- Error: Undefined variable

import prelude/bool
let x = True  -- Error: Undefined variable
```

**Root Cause**:
1. Import desugaring may not be creating correct Core terms
2. Module references may not be resolved during evaluation
3. Selective imports may not be extracting names correctly

**Location**: `src/tao/desugar.gleam` - Import desugaring (lines 468-536)

**Fix Required**:
1. Review import desugaring to Core
2. Verify module reference resolution
3. Test selective import extraction
4. Check evaluation of imported names

---

### Issue 5: Lambda Evaluation

**Problem**: Lambdas with type annotations are not being evaluated correctly.

**Example**:
```tao
let add = fn(x: I32, y: I32) -> I32 { x + y }
add(10, 15)  -- Expected: 25, Actual: ?-1
```

**Root Cause**:
1. Lambda type annotations may not be handled correctly
2. Lambda application may be broken
3. Type annotation may interfere with evaluation

**Location**: `src/tao/desugar.gleam` - Lambda desugaring

**Fix Required**:
1. Review lambda desugaring with type annotations
2. Verify lambda application
3. Test type annotation handling

---

## Implementation Plan

### Phase 1: Fix Grammar Issues (Days 1-2)

1. **Fix function type parsing**
   - Update Type grammar rule to handle nested function types
   - Add tests for function types in parameter annotations
   - Verify parsing of `fn apply(f: fn(I32) -> I32, x: I32)`

2. **Fix match expression parsing**
   - Verify match expression grammar
   - Ensure match can appear anywhere expressions are allowed
   - Test recursive functions with match

### Phase 2: Fix Pattern Matching (Days 3-4)

1. **Review match desugaring**
   - Trace through desugaring of simple match
   - Verify pattern variable binding
   - Test with variable patterns

2. **Fix constructor patterns**
   - Review constructor pattern desugaring
   - Verify constructor name resolution
   - Test with Option/Result types

3. **Fix match guards**
   - Review guard evaluation
   - Verify guard expression desugaring
   - Test with simple guards

### Phase 3: Fix Import System (Days 5-6)

1. **Review import desugaring**
   - Trace through import desugaring
   - Verify Core term generation
   - Test simple imports

2. **Fix selective imports**
   - Review selective import extraction
   - Verify name binding
   - Test with prelude types

3. **Fix module resolution**
   - Review module reference handling
   - Verify module loading
   - Test with prelude modules

### Phase 4: Fix Lambda Evaluation (Day 7)

1. **Review lambda desugaring**
   - Trace through lambda desugaring with type annotations
   - Verify lambda application
   - Test simple lambdas

2. **Fix type annotation handling**
   - Review type annotation processing
   - Verify type annotations don't interfere with evaluation
   - Test with various type annotations

### Phase 5: Testing and Verification (Days 8-9)

1. **Run all tests**
   - Verify all 10 failing tests now pass
   - Check for regressions in passing tests
   - Aim for 515+ tests passing

2. **Update documentation**
   - Update plan status
   - Document any design changes
   - Add examples for fixed features

---

## Success Criteria

- ✅ All 10 failing tests pass
- ✅ No regressions in existing tests (505+ passing)
- ✅ Function types parse correctly
- ✅ Pattern matching evaluates correctly
- ✅ Imports resolve correctly
- ✅ Lambdas evaluate correctly

---

## Risk Mitigation

### Risk 1: Grammar Changes Break Existing Parsing

**Mitigation**:
- Run all tests after each grammar change
- Keep changes minimal and focused
- Test with existing examples

### Risk 2: Desugaring Changes Break Evaluation

**Mitigation**:
- Trace through desugaring step by step
- Test with simple examples first
- Verify Core term output

### Risk 3: Import Changes Break Module Loading

**Mitigation**:
- Test with simple imports first
- Verify module paths are correct
- Check prelude loading

---

## Change Log

| Date | Change | Status |
|------|--------|--------|
| March 18, 2026 | Plan created | 📋 Planned |
| March 18, 2026 | Root cause analysis complete | ✅ Done |
| March 18, 2026 | Implementation plan created | ✅ Done |

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Tao language overview
- **[12-import-system.md](./12-import-system.md)** - Import system specification
- **[13-stmt-system.md](./13-stmt-system.md)** - Stmt system design
- **[07-desugaring-specification.md](./07-desugaring-specification.md)** - Desugaring rules
- **[../core/01-overview.md](../core/01-overview.md)** - Core language
