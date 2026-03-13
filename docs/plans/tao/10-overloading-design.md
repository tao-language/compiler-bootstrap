# Tao Overloading Design

> **Goal**: Support function and operator overloading through dependent types and NbE
> **Status**: 📋 **Design Phase** - Planning before implementation
> **Date**: March 2026

---

## Core Insight

**Overloading is type-directed dispatch**. At compile time, we resolve which implementation to use based on the types of arguments. This can be expressed elegantly using dependent types.

---

## Design Principles

### 1. **Zero-Cost Overloading**

Overloading resolution happens at **compile time**. Runtime code is as efficient as if you called the specific implementation directly.

### 2. **Explicit in Core, Implicit in Tao**

- **Tao source**: `x + y` (implicit)
- **Core term**: `%call (+)(I32, I32)(x, y)` (explicit type application)

### 3. **Composable**

Overloads can be defined in multiple modules and composed together.

---

## Proposed Design

### Tao Source (High-Level)

```tao
// Prelude defines overloaded +
fn (+)(x: I32, y: I32) -> I32 {
  %i32_add(x, y)
}

fn (+)(x: F32, y: F32) -> F32 {
  %f32_add(x, y)
}

// User code
let result = 1 + 2  // I32
let float_result = 1.0 + 2.0  // F32
```

### Core Target (Low-Level)

```core
// Overloaded function as a type-level function
%let (+) = λ(ty: Type) → match ty {
  | {x: %I32, y: %I32} → λ(args) → %call i32_add(args.x, args.y)
  | {x: %F32, y: %F32} → λ(args) → %call f32_add(args.x, args.y)
}

// Usage with type application
%let result = %call (%call (+)(%I32))(1, 2)
%let float_result = %call (%call (+)(%F32))(1.0, 2.0)
```

---

## Key Design Decisions

### 1. **Type Application Strategy**

#### Option A: Explicit Type Arguments (Recommended)

```tao
// Tao surface syntax
1 + 2

// Desugared Tao (intermediate)
(+)(I32, I32)(1, 2)

// Core term
%call (%call (+)(%I32))(1, 2)
```

**Pros**:
- Clear and explicit
- Easy to implement
- Type checking is straightforward
- Similar to System F

**Cons**:
- Verbose in Core
- Type arguments must be inferred or annotated

#### Option B: Implicit Type Resolution

```tao
// Tao surface syntax
1 + 2

// Core term (type inferred from arguments)
%call (+)(1, 2)
```

**Pros**:
- Cleaner Core
- Less verbose

**Cons**:
- Requires sophisticated type inference
- More complex implementation
- May need constraint solving

**Decision**: Start with **Option A** (explicit), potentially optimize to Option B later.

---

### 2. **Overload Resolution Timing**

#### Phase 1: Type Checking (Recommended)

Resolve overloads during type checking, before code generation.

```
Tao Source
    ↓
Parse → Tao AST
    ↓
Type Check + Overload Resolution
    ↓
Core Term (resolved)
    ↓
Evaluate
```

**Pros**:
- Clear separation of concerns
- Error messages at type-check time
- No runtime overhead

**Cons**:
- Requires type information during desugaring

#### Phase 2: Runtime (Not Recommended)

Defer resolution to runtime using type tags.

**Pros**:
- Simpler compiler

**Cons**:
- Runtime overhead
- Loses type safety

**Decision**: **Phase 1** (type-check time resolution).

---

### 3. **Cross-Module Overloads**

#### Problem

```tao
// prelude.tao
fn (+)(x: I32, y: I32) -> I32 { ... }

// vector.tao
fn (+)(v1: Vector, v2: Vector) -> Vector { ... }
```

How do we combine these?

#### Solution: Overload Sets

Each function name maps to an **overload set** containing all implementations.

```
OverloadSet(+) = {
  (I32, I32) → I32: implementation_1,
  (F32, F32) → F32: implementation_2,
  (Vector, Vector) → Vector: implementation_3,
}
```

#### Resolution Algorithm

1. Collect all overloads for the function name (from all imported modules)
2. Filter by argument types
3. If exactly one match, use it
4. If zero matches, error: "no matching overload"
5. If multiple matches, error: "ambiguous overload" (or use specificity rules)

---

### 4. **Function vs Operator Overloading**

#### Same Mechanism

Both functions and operators use the same overloading mechanism:

```tao
// Operator
fn (+)(x: I32, y: I32) -> I32 { ... }

// Function
fn add(x: I32, y: I32) -> I32 { ... }

// Both desugar to the same Core pattern
```

#### Difference: Syntax

- Operators can be used in infix position: `x + y`
- Functions use prefix: `add(x, y)`
- Both support overloading

---

### 5. **Type-Directed Desugaring (Like check_ctr)**

#### Current `check_ctr` Pattern

```gleam
// CtrDef has params that become holes
CtrDef(params: [Param], ...)

// During type checking, params are instanced into holes
// Holes are solved during unification
```

#### Applying to Overloading

```tao
// Tao
fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }

// OverloadDef (similar to CtrDef)
OverloadDef(
  name: "+",
  params: [Param("x", I32), Param("y", I32)],
  return_type: I32,
  body: %i32_add(x, y),
)

// During type checking:
// 1. Create holes for type parameters
// 2. Unify with actual argument types
// 3. Select matching overload
// 4. Generate Core term
```

#### Benefit

- Reuses existing hole-solving infrastructure
- Consistent with other type-checking logic
- Can leverage unification for type inference

---

## Implementation Architecture

### Module Structure

```
src/
├── tao/
│   ├── ast.gleam              # ✅ Existing
│   ├── lexer.gleam            # ✅ Existing
│   ├── syntax.gleam           # ✅ Existing
│   ├── desugar.gleam          # ✅ Existing (needs extension)
│   ├── overloading/           # 📋 NEW
│   │   ├── overload_set.gleam # Overload set data structure
│   │   ├── resolution.gleam   # Overload resolution algorithm
│   │   └── type_app.gleam     # Type application handling
│   └── type_check.gleam       # 📋 NEW (type-directed desugaring)
├── core/
│   └── core.gleam             # May need extensions for type application
```

### Data Structures

#### Overload Set

```gleam
pub type OverloadSet {
  OverloadSet(
    name: String,
    overloads: List(Overload),
  )
}

pub type Overload {
  Overload(
    param_types: List(Type),
    return_type: Type,
    body: Term,  // Core term
    span: Span,
  )
}
```

#### Type Application Term (Core Extension)

```gleam
pub type Term {
  // ... existing constructors
  TypeApp(term: Term, type_args: List(Type), span: Span)  // NEW
}
```

---

## Desugaring Pipeline

### Phase 1: Parse

```tao
// Source
fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }
fn (+)(x: F32, y: F32) -> F32 { %f32_add(x, y) }

let result = 1 + 2
```

```
Tao AST:
- FunctionDef("+", [x: I32, y: I32], I32, body1)
- FunctionDef("+", [x: F32, y: F32], F32, body2)
- Let("result", BinOp("+", 1, 2))
```

### Phase 2: Collect Overloads

```
OverloadEnv:
  "+": OverloadSet([
    Overload([I32, I32], I32, body1),
    Overload([F32, F32], F32, body2),
  ])
```

### Phase 3: Type-Directed Desugaring

```tao
// Expression: 1 + 2
// Type of 1: I32, Type of 2: I32
// Resolve: (+)(I32, I32)

// Desugared:
(+)(I32, I32)(1, 2)
```

### Phase 4: Core Generation

```core
%let (+) = λ(ty: Type) → match ty {
  | {x: %I32, y: %I32} → λ(args) → %call i32_add(args.x, args.y)
  | {x: %F32, y: %F32} → λ(args) → %call f32_add(args.x, args.y)
}

%let result = %call (%call (+)(%I32))(1, 2)
```

---

## Type Inference Integration

### Problem

How do we infer types for:

```tao
let x = 1 + 2  // What type is x?
```

### Solution: Bidirectional Type Checking

```gleam
// Check mode: verify expression has expected type
fn check(expr: Expr, expected: Type) -> Result(Term, Error)

// Infer mode: infer type from expression
fn infer(expr: Expr) -> Result(#(Term, Type), Error)

// For overloaded operators:
fn infer(BinOp("+", left, right)) {
  let #(left_term, left_ty) = infer(left)
  let #(right_term, right_ty) = infer(right)
  
  // Resolve overload based on argument types
  let resolved = resolve_overload("+", [left_ty, right_ty])
  
  case resolved {
    Ok(overload) -> {
      let term = make_type_app(overload, [left_ty, right_ty], [left_term, right_term])
      Ok(#(term, overload.return_type))
    }
    Error(_) -> Error(NoMatchingOverload)
  }
}
```

---

## Open Questions & Decisions

### Q1: Should ALL functions use type application?

**Answer**: No, only overloaded functions.

```tao
// Non-overloaded function (no type application needed)
fn double(x: I32) -> I32 { x * 2 }
double(5)  // Desugars to: %call double(5)

// Overloaded function (type application needed)
fn (+)(x: I32, y: I32) -> I32 { ... }
fn (+)(x: F32, y: F32) -> F32 { ... }
1 + 2  // Desugars to: %call (%call (+)(%I32))(1, 2)
```

### Q2: When does type augmentation happen?

**Answer**: During Tao type checking (before Core generation).

```
Tao AST → [Type Check + Overload Resolution] → Core Term
                                    ↓
                            Insert type applications
```

### Q3: How to handle cross-module overloads?

**Answer**: Overload sets are merged at import time.

```tao
// module_a.tao
export fn (+)(x: I32, y: I32) -> I32 { ... }

// module_b.tao
export fn (+)(x: Vector, y: Vector) -> Vector { ... }

// main.tao
import module_a
import module_b

// Both + overloads are available
let x = 1 + 2           // Uses I32 version
let v = v1 + v2         // Uses Vector version
```

### Q4: Can we avoid explicit type arguments?

**Answer**: Potentially, using constraint solving (future optimization).

```tao
// Current (explicit)
(+)(I32, I32)(1, 2)

// Future (implicit, if feasible)
(+) { _ = 1, _ = 2 }  // Type inferred from context
```

This would require:
1. Constraint generation during type checking
2. Constraint solving (unification)
3. Type reconstruction

**Decision**: Start with explicit, add implicit later if needed.

---

## Core Changes Required

### 1. Type Application Term

```gleam
pub type Term {
  // ... existing
  TypeApp(term: Term, types: List(Type), span: Span)  // NEW
}
```

### 2. Type Application Evaluation

```gleam
pub fn eval(ffi, env, term) -> Value {
  case term {
    TypeApp(func, types, _) -> {
      // Evaluate type application
      // Types are erased at runtime, just evaluate the function
      eval(ffi, env, func)
    }
    // ...
  }
}
```

### 3. Type Application in Type Checker

```gleam
pub fn infer(state, term) -> #(InferResult, State) {
  case term {
    TypeApp(func, types, _) -> {
      // Check that func accepts these type arguments
      // Return instantiated type
    }
    // ...
  }
}
```

---

## Implementation Phases

### Phase 1: Core Extensions (1 week)

- [ ] Add `TypeApp` constructor to `Term`
- [ ] Add `TypeApp` evaluation
- [ ] Add `TypeApp` type checking
- [ ] Tests for type application

### Phase 2: Overload Sets (1 week)

- [ ] Define `OverloadSet` data structure
- [ ] Define `Overload` data structure
- [ ] Overload collection from AST
- [ ] Cross-module overload merging

### Phase 3: Overload Resolution (1-2 weeks)

- [ ] Resolution algorithm
- [ ] Type-directed desugaring
- [ ] Error reporting (no match, ambiguous)
- [ ] Tests for resolution

### Phase 4: Tao Integration (1 week)

- [ ] Parse overloaded function definitions
- [ ] Parse operator usage (infix)
- [ ] Desugar to type applications
- [ ] End-to-end tests

### Phase 5: Polish (1 week)

- [ ] Documentation
- [ ] Examples (Vector, Matrix, etc.)
- [ ] Performance optimization
- [ ] Bug fixes

**Total**: 5-6 weeks

---

## Examples

### Example 1: Basic Overloading

```tao
// Source
fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }
fn (+)(x: F32, y: F32) -> F32 { %f32_add(x, y) }

let a = 1 + 2
let b = 1.0 + 2.0
```

```core
// Desugared
%let (+) = λ(ty) → match ty {
  | {x: %I32, y: %I32} → λ(args) → %call i32_add(args.x, args.y)
  | {x: %F32, y: %F32} → λ(args) → %call f32_add(args.x, args.y)
}

%let a = %call (%call (+)(%I32))(1, 2)
%let b = %call (%call (+)(%F32))(1.0, 2.0)
```

### Example 2: Vector Addition

```tao
// vector.tao
type Vector = Vector(x: F32, y: F32)

fn (+)(v1: Vector, v2: Vector) -> Vector {
  Vector(x: v1.x + v2.x, y: v1.y + v2.y)
}
```

```core
// Desugared (simplified)
%let (+) = λ(ty) → match ty {
  | {v1: Vector, v2: Vector} → λ(args) → 
      %let v1 = args.v1
      %let v2 = args.v2
      %let sum_x = %call (%call (+)(%F32))(v1.x, v2.x)
      %let sum_y = %call (%call (+)(%F32))(v1.y, v2.y)
      Vector(sum_x, sum_y)
}
```

### Example 3: Cross-Module

```tao
// prelude.tao
export fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }
export fn (+)(x: F32, y: F32) -> F32 { %f32_add(x, y) }

// vector.tao
import prelude

type Vector = Vector(x: F32, y: F32)

export fn (+)(v1: Vector, v2: Vector) -> Vector {
  // Uses prelude's + for F32 internally
  Vector(x: v1.x + v2.x, y: v1.y + v2.y)
}
```

---

## Risks & Mitigations

### Risk 1: Complexity

**Mitigation**: Start with simple cases (single module, no inference), add complexity incrementally.

### Risk 2: Performance

**Mitigation**: Type applications are erased at runtime. Resolution happens at compile time.

### Risk 3: Error Messages

**Mitigation**: Provide clear error messages for "no matching overload" and "ambiguous overload".

### Risk 4: Core Bloat

**Mitigation**: Type applications add some verbosity, but this is acceptable for the flexibility gained.

---

## Related Documents

- **[09-tao-mvp-plan.md](./09-tao-mvp-plan.md)** - Tao MVP (completed)
- **[03-desugaring.md](./03-desugaring.md)** - Desugaring rules (needs update)
- **[../../docs/core.md](../../docs/core.md)** - Core language spec (needs update)
- **[../../docs/plans/core/](../../docs/plans/core/)** - Core plans (may need updates)

---

## Decision Summary

| Question | Decision |
|----------|----------|
| Type application strategy | Explicit (Option A) |
| Resolution timing | Type-check time |
| Cross-module overloads | Overload sets merged at import |
| Function vs operator | Same mechanism |
| Use hole-solving like check_ctr | Yes, leverage existing infrastructure |
| All functions use type app? | No, only overloaded |
| Implicit type resolution? | Future optimization |

---

**This design provides a solid foundation for overloading while maintaining simplicity and performance.** 🎯
