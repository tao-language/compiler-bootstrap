# Type Annotations and Constructor Registration Fix

> **Goal**: Properly desugar type annotations and register type definitions in Core
> **Status**: 🚧 **In Progress** - Phase 1-3 complete, Phase 4 needs refinement
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
4. Fix type checker to use annotations instead of creating holes

---

## Current Status

### ✅ Phase 1: Type Annotations (COMPLETE)

**Completed**:
- Created `build_core_type_from_ast()` function to convert `TypeAst` to `CoreTerm`
- Created `build_fn_type()` for building Pi types
- Added `CorePi` constructor to desugar `CoreTerm` type
- Added `core_term_to_term_loop` handling for `CorePi`

**Issues**:
- Function type annotations with holes for unannotated parameters cause InfiniteType errors
- Currently disabled - annotations are parsed but not added as `CoreAnn`

### ✅ Phase 2: Constructor Registration (COMPLETE)

**Completed**:
- Modified `process_type_definitions()` to register type constructors (e.g., `Bool` itself, not just `True`/`False`)
- Created `state_with_constructors()` to merge `DesugarContext.ctrs` into `State.ctrs`
- Updated `test_api.gleam` to use constructor environment

**Result**: Type constructors like `Bool`, `Option`, `Result` are now properly registered and available during type checking.

### ✅ Phase 3: Type Checker Fixes (COMPLETE)

**Completed**:
- Modified `check(Fix)` to use expected type instead of creating a hole
- Modified `check(Lam)` to use domain type from expected `VPi` instead of creating a hole
- Fixed `infer(Ann)` to use `eval` instead of `infer` for annotation types

**Issues**:
- The fixes help but don't fully solve the InfiniteType error
- The root cause is that Pi type annotations contain holes for unannotated parameters
- These holes appear in the inferred type and fail the occurs check

### 🚧 Phase 4: Proper Hole Handling (IN PROGRESS)

**TODO**:
- Fix hole handling in Pi type annotations
- Either: don't create holes for unannotated parameters, or properly solve them during unification
- Alternative: only annotate with return type, let type checker infer parameter types

---

## Implementation Progress

### Completed Changes

#### 1. Type Building Functions (`src/tao/desugar.gleam`)

```gleam
/// Convert Tao TypeAst to Core type term for type annotations.
fn build_core_type_from_ast(t: TypeAst, dc: DesugarContext, span: Span) 
  -> #(CoreTerm, DesugarContext)

/// Build function type from parameter types and return type.
/// For a function (a: A, b: B) -> C, builds: Pi(_, A, Pi(_, B, C))
fn build_fn_type(param_types: List(CoreTerm), ret_type: CoreTerm, span: Span) -> CoreTerm
```

#### 2. CorePi Constructor (`src/tao/desugar.gleam`)

```gleam
pub type CoreTerm {
  // ...
  /// Pi type (dependent function type)
  CorePi(implicit: List(String), name: String, domain: CoreTerm, codomain: CoreTerm, span: Span)
  // ...
}
```

#### 3. Constructor Registration (`src/tao/desugar.gleam`)

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

#### 4. State Initialization (`src/tao/test_api.gleam`)

```gleam
/// Initialize Core State with constructor environment from desugaring.
fn state_with_constructors(dc: DesugarContext, initial: core.State) -> core.State {
  let merged_ctrs = list.append(dc.ctrs, initial.ctrs)
  core.State(..initial, ctrs: merged_ctrs)
}
```

#### 5. Core Type Checker Fixes (`src/core/core.gleam`)

```gleam
pub fn check(s: State, term: Term, expected_ty: Type, ty_span: Span) -> #(Value, State) {
  case term {
    Fix(name, body, span) -> {
      // Fixpoint with expected type: use the expected type instead of creating a hole
      let env = get_env(s)
      let #(_fresh, s) = def_var(s, name, expected_ty)
      let #(body_val, s) = check(s, body, expected_ty, span)
      let fix_val = VFix(name, env, body)
      #(fix_val, s)
    }
    Lam(implicit, param, body, span) -> {
      // Lambda with expected VPi type: use the domain type from the VPi
      case expected_ty {
        VPi(_, _, _, domain, codomain) -> {
          let #(_fresh, s) = def_var(s, param.0, domain)
          let codomain_val = eval(s.ffi, get_env(s), codomain)
          let #(body_val, s) = check(s, body, codomain_val, span)
          let lam_val = VLam(implicit, param.0, get_env(s), body)
          #(lam_val, s)
        }
        _ -> { /* infer and unify */ }
      }
    }
    _ -> { /* infer and unify */ }
  }
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
1. Function type annotations are built with holes for unannotated parameter types
2. When the Pi type is evaluated, holes become `VNeut(HHole)` values
3. These holes appear in the inferred type
4. The occurs check fails when trying to unify a hole with a type containing the same hole

**Current Workaround**: Function type annotations are disabled. The type checker relies on constructor environment for type inference.

**Required Fix** (options):
1. **Option A**: Don't create holes for unannotated parameters - use a different mechanism
2. **Option B**: Properly solve holes during unification before the occurs check
3. **Option C**: Only annotate with return type, let type checker infer parameter types from context

---

## Test Results

| Test | Status | Notes |
|------|--------|-------|
| `lib_prelude_bool_module_test` | ❌ FAIL | InfiniteType error |
| `core examples` | ⚠️ MIXED | 1 failure (pattern mismatch - unrelated) |
| `tao examples` | ⚠️ MIXED | 4 failures (nested_fn, higher_order, recursive_fn) |
| **Total** | **519 passed, 5 failures** | Down from 523/1 |

---

## Next Steps

### Immediate (Phase 4)

1. **Disable function type annotations** temporarily to unblock other work
2. **Investigate hole solving** during unification
3. **Consider alternative annotation strategy** - annotate lambda body instead of fixpoint

### Medium Term

1. **Implement proper Pi type unification** that handles holes correctly
2. **Add tests** for type annotations with various parameter combinations
3. **Document** the type annotation semantics

### Long Term

1. **Support dependent types** fully with proper Pi type handling
2. **Optimize** type inference to minimize hole creation
3. **Add type-directed desugaring** for better error messages

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
| March 2026 | Phase 3 implemented (check fixes) |
| March 2026 | Updated status: Phase 1-3 complete, Phase 4 needs refinement |
