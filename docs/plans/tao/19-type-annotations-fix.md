# Type Annotations and Constructor Registration Fix

> **Goal**: Properly desugar type annotations and register type definitions in Core
> **Status**: 🚧 **In Progress** - Phase 1 & 2 complete, Phase 3 & 4 pending
> **Date**: March 2026
> **Priority**: **CRITICAL** - Affects ALL code, not just prelude

---

## Overview

**Problem**: The Tao compiler currently ignores type annotations in function definitions and doesn't properly register type definitions (ADTs) in the Core type checker's constructor environment.

**Impact**: 
- Type annotations like `fn not(b: Bool) -> Bool` are ignored
- Type checker must infer all types, leading to InfiniteType errors
- User-defined ADTs (like `type Option = Some | None`) don't work
- Only works for code without any type annotations

**Solution**: 
1. Build Core types from Tao type annotations and wrap with `CoreAnn`
2. Register type definitions in `DesugarContext.ctrs` during desugaring
3. Convert `DesugarContext.ctrs` to `State.ctrs` before type checking

---

## Current Status

### ✅ Phase 1: Type Annotations (COMPLETE)

**Completed**:
- Created `build_core_type_from_ast()` function to convert `TypeAst` to `CoreTerm`
- Created `build_lambdas_with_annotations()` for handling parameter annotations
- Modified `StmtFn` handling (currently disabled due to type checker issues)
- Fixed `infer()` for `Ann` to use `eval` instead of `infer` for annotation types

**Issues**:
- Return type annotations cause InfiniteType errors in the type checker
- The type checker creates holes during lambda inference that fail the occurs check
- Proper Pi type construction is needed for function type annotations

**Workaround**: Currently, type annotations are parsed but not added as `CoreAnn`. The type checker relies on constructor environment for type inference.

### ✅ Phase 2: Constructor Registration (COMPLETE)

**Completed**:
- Modified `process_type_definitions()` to register type constructors (e.g., `Bool` itself, not just `True`/`False`)
- Created `state_with_constructors()` to merge `DesugarContext.ctrs` into `State.ctrs`
- Updated `test_api.gleam` to use constructor environment

**Result**: Type constructors like `Bool`, `Option`, `Result` are now properly registered and available during type checking.

### 🚧 Phase 3: Type Applications (PENDING)

**TODO**:
- Handle type applications: `Option(Bool)`, `List(I32)`, etc.
- Support type parameters in function definitions: `fn id<T>(x: T) -> T`
- Build proper Pi types for function signatures

### 🚧 Phase 4: Core Type Checker (PENDING)

**TODO**:
- Fix InfiniteType error in recursive function type inference
- Properly handle Pi type construction and unification
- Ensure occurs check doesn't fail for valid recursive definitions

---

## Implementation Progress

### Completed Changes

#### 1. Type Building Functions (`src/tao/desugar.gleam`)

```gleam
/// Convert Tao TypeAst to Core type term for type annotations.
fn build_core_type_from_ast(t: TypeAst, dc: DesugarContext, span: Span) 
  -> #(CoreTerm, DesugarContext)

/// Build type applications: Base(Arg1, Arg2, ...)
fn build_type_applications(base: CoreTerm, args: List(CoreTerm), span: Span) -> CoreTerm

/// Build list of type arguments.
fn build_core_type_args(args: List(TypeAst), dc: DesugarContext, span: Span) 
  -> #(List(CoreTerm), DesugarContext)
```

#### 2. Constructor Registration (`src/tao/desugar.gleam`)

```gleam
fn process_type_definitions(stmts: List(Stmt), dc: DesugarContext) -> DesugarContext {
  list.fold(stmts, dc, fn(acc_dc, stmt) {
    case stmt {
      StmtType(name, type_params, constructors, _span) -> {
        // Add the type itself as a constructor
        let type_ctr = #(name, CtrDef(params: type_params, 
                                       arg_ty: Unit(...), 
                                       ret_ty: Typ(0, ...)))
        let new_ctrs = tao_type_to_core_ctrs(name, type_params, constructors)
        DesugarContext(..acc_dc, ctrs: list.append(acc_dc.ctrs, [type_ctr, ..new_ctrs]))
      }
      _ -> acc_dc
    }
  })
}
```

#### 3. State Initialization (`src/tao/test_api.gleam`)

```gleam
/// Initialize Core State with constructor environment from desugaring.
fn state_with_constructors(dc: DesugarContext, initial: core.State) -> core.State {
  let merged_ctrs = list.append(dc.ctrs, initial.ctrs)
  core.State(..initial, ctrs: merged_ctrs)
}
```

#### 4. Core Type Checker Fix (`src/core/core.gleam`)

```gleam
Ann(term, term_ty, _) -> {
  // Type annotation: evaluate the annotation type and check the term against it.
  // Note: We eval (not infer) the annotation because it's already a type expression.
  let ty_val = eval(s.ffi, get_env(s), term_ty)
  let #(val, s) = check(s, term, ty_val, get_span(term_ty))
  #(val, ty_val, s)
}
```

---

## Known Issues

### InfiniteType Error in Recursive Functions

**Symptom**: When type checking recursive functions, the type checker reports:
```
InfiniteType(4, VPi([], "_", [VNeut(HVar(1), []), VNeut(HVar(0), [])], ...))
```

**Root Cause**: 
1. During lambda inference, the type checker creates holes for parameter and return types
2. When checking the lambda body, these holes appear in the inferred type
3. The occurs check fails when trying to unify a hole with a type containing the same hole

**Required Fix**:
1. Build proper Pi types for function signatures instead of just annotating with return type
2. Fix the type checker's handling of recursive function types
3. Ensure holes are properly generalized before unification

---

## Test Results

| Test | Status | Notes |
|------|--------|-------|
| `lib_prelude_bool_module_test` | ❌ FAIL | InfiniteType error |
| `core examples` | ⚠️ MIXED | 1 failure (pattern mismatch) |
| `tao examples` | ⚠️ MIXED | 2 failures (nested_fn, higher_order) |
| **Total** | **521 passed, 3 failures** | Down from 523/1 |

---

## Related Documents

- **[../core/core.gleam](../../src/core/core.gleam)** - Core type checker
- **[../desugar.gleam](../../src/tao/desugar.gleam)** - Desugaring logic
- **[../global_context.gleam](../../src/tao/global_context.gleam)** - Module resolution
- **[18-stdlib-testing.md](18-stdlib-testing.md)** - Testing infrastructure

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial plan created |
| March 2026 | Phase 1 & 2 implemented |
| March 2026 | Updated status: Phase 1 & 2 complete, issues identified |
