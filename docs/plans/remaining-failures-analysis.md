# Comprehensive Analysis of Remaining 5 Test Failures

**Date**: April 5, 2026
**Status**: 439 passed, 5 failures
**Commit**: bf03fe5

---

## Executive Summary

All 5 failures trace to **two distinct root causes**:

1. **4 failures**: Multi-function cross-reference type mismatch in `check_ctr_def` sequential processing
2. **1 failure**: TypeDecl grammar doesn't support polymorphic type parameters

---

## Issue 1: Multi-function Cross-Reference Type Mismatch

### Affected Tests (4)

| Test | Module | Error |
|------|--------|-------|
| `lib_prelude_bool_module_test` | `lib/prelude/bool.tao` | TypeMismatch + NotAFunction |
| `match_different_result_types_test` | Inline | AssertionError |
| `three_match_expressions_no_conflict_test` | Inline | AssertionError |
| `match_different_types_test` | Inline | AssertionError |

### Exact Error (from lib_prelude_bool_module_test)

```
TypeMismatch(
  VPi([], "_", 
    [VNeut(HVar(4), [EApp(VNeut(HVar(4), [])), EApp(VNeut(HVar(5), []))]),
     VNeut(HVar(3), []), VNeut(HVar(2), []), VNeut(HVar(1), []), VNeut(HVar(0), [])],
    VCtrValue(VCtr("Bool", VUnit)),
    Hole(0, Span("lib/prelude/bool.tao", 0, 0, 0, 0))),
  VCtrValue(VCtr("Bool", VUnit)),
  Span("", 0, 0, 0, 0),
  Span("lib/prelude/bool.tao", 36, 17, 36, 20)
)
NotAFunction(Var(4, Span("lib/prelude/bool.tao", 36, 7, 36, 9)),
             VCtrValue(VCtr("Bool", VUnit)))
```

### Error Interpretation

- **Position**: Line 36, cols 7-9 = `or` in `and(or(a, b), not(and(a, b)))`
- **Expected**: `or` should have type `Bool -> Bool -> Bool`
- **Actual**: `or` has type `Bool` (a constructor value)
- **NotAFunction**: Var(4) = `or` is being called but has type `Bool`
- **TypeMismatch**: A VPi (function type) is being compared with `Bool`

### Module Structure (bool.tao)

```
type Bool = True | False        // Type definition
fn not(b: Bool) -> Bool         // Function 1: uses match
fn and(a: Bool, b: Bool) -> Bool // Function 2: uses match
fn or(a: Bool, b: Bool) -> Bool  // Function 3: uses match, called by xor
fn xor(a: Bool, b: Bool) -> Bool // Function 4: calls and, or, not
```

### Desugared AST Structure

The desugarer produces this structure for sequential function definitions:

```
DoBlock(
  [ // prelude imports (skipped for type-def modules)
    Let(not, Fix(not, Lam(b, match_body)), span),
    Let(and, Fix(and, Lam(a, Lam(b, match_body))), span),
    Let(or, Fix(or, Lam(a, Lam(b, match_body))), span),
    Let(xor, Fix(xor, Lam(a, Lam(b, call_body))), span)
  ],
  Rcd([not, and, or, xor]),
  span
)
```

Which becomes (via `build_sequential_loop`):

```
App(
  Lam(not, Some(Bool -> Bool),
    App(
      Lam(and, Some(Bool -> Bool -> Bool),
        App(
          Lam(or, Some(Bool -> Bool -> Bool),
            App(
              Lam(xor, Some(Bool -> Bool -> Bool),
                Rcd([not, and, or, xor])),
              Fix(xor, Lam(a, Lam(b, call_body))))),
          Fix(or, Lam(a, Lam(b, match_body))))),
      Fix(and, Lam(a, Lam(b, match_body))))),
  Fix(not, Lam(b, match_body)))
```

### Type-Checker Processing Flow

When the type-checker processes this nested App/Lam/Fix structure:

1. **Outer App**: `App(Lam(not, ...), Fix(not, ...))`
   - `infer` processes Lam(not) → binds `not` with type `Bool -> Bool`
   - `infer` processes Fix(not) → body checked against annotation

2. **Next App**: `App(Lam(and, ...), Fix(and, ...))`
   - Lam(and) → binds `and` with type `Bool -> Bool -> Bool`
   - Fix(and) → body checked against annotation

3. **Next App**: `App(Lam(or, ...), Fix(or, ...))`
   - Lam(or) → binds `or` with type `Bool -> Bool -> Bool`
   - Fix(or) → body checked against annotation

4. **Inner App**: `App(Lam(xor, ...), Fix(xor, ...))`
   - Lam(xor) → binds `xor` with type `Bool -> Bool -> Bool`
   - Fix(xor) → body checked against annotation
   - **Body**: `call_body = and(or(a, b), not(and(a, b)))`
   - When type-checking `and(or(a, b), ...)`:
     - Looks up `and` → should be `Bool -> Bool -> Bool`
     - Looks up `or` → should be `Bool -> Bool -> Bool`
     - **But Var(4) = `or` has type `Bool`!**

### Root Cause Hypothesis

The issue is in how `check` processes the nested App structure. When checking `Fix(xor, ...)`:

1. The `check` function sees `Fix(name, body, span)` with expected type
2. My fix (Fix #11) detects `Ann(_, ann_ty, _)` and uses `ann_ty` for `def_var`
3. But the `body` of `Fix(xor, ...)` is NOT an `Ann` — it's the actual function body
4. The annotation type is on the **outer Lam**, not on the Fix body

The structure is:
```
App(Lam(xor, Some(ann_ty), App(Fix(xor, body), ...)), ...)
```

The Fix body is checked against the Lam's parameter type, but the Fix's `def_var` might be using the wrong type.

### Traced Issue

Looking at the exact error position (36, 17-20), this is in the `or` function body. The VPi in the TypeMismatch has:
- 5 HVar entries in its env: HVar(4), HVar(3), HVar(2), HVar(1), HVar(0)
- These represent 5 outer bindings

But the `or` function should see:
- `b` (param), `a` (param), `or` (self), `or` (outer), `and`, `not`

That's 6 bindings, not 5. The HVar indices suggest something is off by one.

### Attempted Fixes

1. **Fix #11** (committed): Modified `check` for `Fix` to use annotation type for `def_var`
   - **Result**: Didn't resolve the issue
   - **Why**: The annotation is on the Lam, not the Fix body

### Recommended Investigation Steps

1. **Trace the exact AST structure** for bool.tao after desugaring
2. **Add debug logging** to `check` to print:
   - The term being checked
   - The expected type
   - The current vars list
   - The env length
3. **Identify** where Var(4)'s type becomes `Bool` instead of `Bool -> Bool -> Bool`

### Approaches to Fix

| Approach | Description | Complexity | Risk |
|----------|-------------|----------|------|
| **A** | Add debug logging to pinpoint exact wrong unification | Low | Low |
| **B** | Fix how `build_sequential_loop` structures nested Apps | Medium | Medium |
| **C** | Fix how `check` handles nested App(Lam, Fix) structures | Medium | Medium |
| **D** | Change desugarer to use different structure for sequential defs | High | High |

**Recommendation**: Start with Approach A (debug logging), then fix based on findings.

---

## Issue 2: TypeDecl Grammar Doesn't Support Type Parameters

### Affected Test (1)

| Test | Error |
|------|-------|
| `local_option_shadows_prelude_test` | ParseError at `type Option(a)` |

### Root Cause

The TypeDecl grammar rule uses `TIdent` for the type name:

```
type_decl:
  "type" TIdent "=" (constructor "|")+ ";"
```

So `type Option = Some(a) | None` works, but `type Option(a) = Some(a) | None` fails because `(a)` after the type name is not consumed.

### Fix

Update the TypeDecl grammar rule to support optional type parameters:

```
type_decl:
  "type" TIdent "(" TIdent ")" "=" (constructor "|")+ ";"
  | "type" TIdent "=" (constructor "|")+ ";"
```

This requires:
1. Modifying the `type_decl` rule in `src/tao/syntax.gleam`
2. Updating the AST extraction to handle the optional type parameter
3. Updating the desugarer to handle type parameters (currently ignored)

**Complexity**: Low — straightforward grammar change
**Risk**: Low — additive change, doesn't affect existing code

---

## Detailed Step-by-Step Plan

### Phase 1: Fix TypeDecl Grammar (Issue 2) — Estimated 1-2 hours

**Step 1**: Update `type_decl` grammar rule
- Add alternative rule with type parameters
- Parse `type Name(param) = ...` syntax

**Step 2**: Update AST extraction
- Handle both `TypeDecl(name, constructors)` and `TypeDecl(name, param, constructors)`
- Store type parameter in AST

**Step 3**: Write unit tests
- Test: `type Option(a) = Some(a) | None` parses correctly
- Test: `type Result(a, b) = Ok(a) | Err(b)` parses correctly
- Test: `type Option = Some | None` (no params) still works
- Test: Type parameter shadows prelude type

**Step 4**: Run full test suite
- Verify no regressions
- Verify `local_option_shadows_prelude_test` passes

### Phase 2: Debug Multi-function Type Mismatch (Issue 1) — Estimated 2-4 hours

**Step 5**: Add targeted debug logging
- Modify `check` to print term, expected type, vars list
- Run bool.tao test to see actual values
- Identify where Var(4)'s type becomes wrong

**Step 6**: Analyze debug output
- Trace the exact point where the wrong type is assigned
- Determine if it's in `check`, `infer`, or `check_ctr_def`

**Step 7**: Implement fix based on findings
- Likely in `check` for App(Lam, Fix) structures
- Or in `build_sequential_loop` structure

**Step 8**: Write unit tests
- Test: Single function with match
- Test: Two functions, no cross-reference
- Test: Two functions, cross-reference
- Test: Three functions, chain cross-reference
- Test: Full bool module (not, and, or, xor)

**Step 9**: Run full test suite
- Verify all 5 failures are fixed
- Verify no regressions

---

## Edge Cases to Consider

### For Issue 1 (Multi-function):

1. **Single function, no match** — baseline, should work
2. **Single function, with match** — should work
3. **Two functions, no cross-reference** — should work
4. **Two functions, one references the other** — fails
5. **Three functions, chain: A→B→C** — fails
6. **Three functions, all reference each other** — fails
7. **Recursive function calling itself** — should work (Fix handles this)
8. **Nested function calls: f(g(h(x)))** — edge case
9. **Function with multiple params: f(a, b) calls g(c, d)** — edge case
10. **Module with type def + single function** — should work

### For Issue 2 (TypeDecl):

1. **No type params**: `type Bool = True | False` — should work
2. **One type param**: `type Option(a) = Some(a) | None` — should work
3. **Two type params**: `type Result(a, b) = Ok(a) | Err(b)` — should work
4. **Type param used in constructor**: `Some(a)` — should work
5. **Type param NOT used**: `type Unit(a) = Unit` — should work
6. **Type param shadows prelude**: `type Bool(a) = True | False` — should work
7. **Multiple type decls in same module** — should work

---

## Current Status Summary

| Component | Status | Notes |
|-----------|--------|-------|
| TypeDecl grammar | ❌ No type param support | Simple fix needed |
| Multi-function types | ❌ Wrong types for cross-refs | Debug logging needed |
| Single function | ✅ Works | |
| Match expressions | ✅ Works (single function) | |
| Constructor resolution | ✅ Works | |
| Match motive holes | ✅ Works | Fixed in b344d8e |

**Next Action**: Fix TypeDecl grammar (Phase 1), then debug multi-function issue (Phase 2).
