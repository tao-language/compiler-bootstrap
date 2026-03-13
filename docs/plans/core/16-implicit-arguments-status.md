# Core Implicit Arguments - Implementation Status

> **Goal**: Support function and operator overloading through implicit arguments
> **Status**: 🔄 **In Progress** - Core AST complete, syntax updates in progress
> **Date**: March 2026

---

## Design Summary

### Key Design Decisions

1. **Unified Implicit Handling**: `Lam`, `App`, and `Pi` all have implicit parameter lists
2. **Forall Merged into Pi**: No separate Forall constructor - implicit params are part of Pi
3. **Backward Compatible**: Empty implicit lists are omitted in syntax
4. **Type Erasure**: Implicit args erased at runtime

### Syntax

```
// Lambda with implicit type params
%fn<T>(x) -> body          // Polymorphic function
%fn(x) -> body             // Regular function (no implicits)

// Application with implicit args
f<T>(x)                    // Type application
f(x)                       // Regular application

// Pi type with implicit params
%pi<T>(x: A) -> B          // Polymorphic function type
%pi(x: A) -> B             // Regular function type
```

---

## AST Structure

### Term
```gleam
Lam(implicit: List(String), param: #(String, Term), body: Term)
App(fun: Term, implicit: List(Term), arg: Term)
Pi(implicit: List(String), name: String, in_term: Term, out_term: Term)
```

### Value (Type)
```gleam
VLam(implicit: List(String), name: String, env: Env, body: Term)
VPi(implicit: List(String), name: String, env: Env, in_val: Value, out_term: Term)
```

---

## Implementation Status

### ✅ Complete

| Component | Status | Notes |
|-----------|--------|-------|
| **Core AST** | ✅ Complete | Lam, App, Pi with implicit lists |
| **Evaluation** | ✅ Complete | Recursive implicit handling, erasure |
| **Type Inference** | ✅ Complete | Automatic Forall via Pi |
| **Quote** | ✅ Complete | Preserves implicit info |
| **Formatter** | ✅ Complete | `%fn<T>(x)` syntax |

### 🔄 In Progress

| Component | Status | Notes |
|-----------|--------|-------|
| **Parser** | 🔄 In Progress | Need grammar for `<T>` syntax |
| **NamedTerm** | 🔄 In Progress | Add implicit fields |
| **Core Tests** | 🔄 Pending | Update Lam/App/Pi calls |
| **Syntax Tests** | 🔄 Pending | Update after parser |
| **Tao Integration** | 🔄 Pending | Update desugarer |

### 📋 Pending

| Component | Status | Notes |
|-----------|--------|-------|
| **Overloading Examples** | 📋 Pending | Demonstrate overloading |
| **Documentation** | 📋 Pending | Update user docs |

---

## Implementation Phases

### Phase 1: Core AST ✅ (Complete)
- [x] Update Lam with implicit list
- [x] Update App with implicit list
- [x] Merge Forall into Pi
- [x] Update VLam/VPi in Value

### Phase 2: Evaluation ✅ (Complete)
- [x] Recursive implicit handling in eval
- [x] Implicit argument erasure
- [x] Update do_app_implicit
- [x] Update apply_spine

### Phase 3: Type Inference ✅ (Complete)
- [x] Lam infers to VPi with implicits
- [x] App instantiates implicit params
- [x] Unification handles VPi with implicits
- [x] Occurs check updated

### Phase 4: Quote ✅ (Complete)
- [x] Quote VLam with implicits
- [x] Quote VPi with implicits
- [x] Handle EAppImplicit in spine

### Phase 5: Syntax 🔄 (In Progress)
- [ ] Add implicit fields to NamedTerm
- [ ] Parser grammar for `%fn<T>(x)`
- [ ] Parser grammar for `f<T>(x)`
- [ ] Parser grammar for `%pi<T>(x)`
- [ ] Formatter outputs implicit syntax

### Phase 6: Core Tests 🔄 (Pending)
- [ ] Update test/core/core_test.gleam
- [ ] Update test/core/infer_test.gleam
- [ ] Update test/core/eval_test.gleam

### Phase 7: Integration 🔄 (Pending)
- [ ] Update Tao desugarer
- [ ] End-to-end tests
- [ ] Overloading examples

---

## Type Inference Behavior

### Polymorphic Identity

```
Term:  Lam(["T"], #("x", Hole), Var("x"))
Infers to: VPi(["T"], "x", _, Var("x"))
Type:    ∀T. T → T
```

### Application

```
Term:  App(id, ["I32"], Lit(42))
id:    VPi(["T"], "x", _, Var("x"))
Result: I32
```

---

## Open Questions

### Resolved

1. **Forall vs Pi**: ✅ Merged into Pi with implicit list
2. **NamedTerm implicits**: ✅ Will add implicit fields
3. **Parser syntax**: ✅ `%fn<T>(x)` and `f<T>(x)`
4. **Test strategy**: ✅ Core tests first, then syntax/tests

### Remaining

1. **Pi syntax**: Should it be `%pi` or `(x: A) -> B`?
   - **Decision**: Support both - `%pi` for explicit, `->` for implicit
   
2. **Implicit param types**: How to specify type of implicit params?
   - **Decision**: Infer from usage, or add explicit syntax later

---

## Related Documents

- **[../tao/10-overloading-design.md](../tao/10-overloading-design.md)** - Overloading design
- **[../tao/11-overloading-implementation.md](../tao/11-overloading-implementation.md)** - Implementation plan
- **[../../docs/core.md](../../docs/core.md)** - Core language spec

---

**Last Updated**: March 2026 - Forall merged into Pi
