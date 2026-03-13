# Tao Overloading Implementation Guide

> **Status**: 📋 **Design Complete, Implementation Pending**
> **Date**: March 2026

---

## Overview

This document describes how to implement function and operator overloading in Tao using the implicit argument mechanism that has been added to Core.

---

## Core Mechanism

### Implicit Arguments in Core

Core now supports implicit arguments in `Lam`, `App`, and `Pi`:

```gleam
// Core AST
Lam(implicit: List(String), param: #(String, Term), body: Term)
App(fun: Term, implicit: List(Term), arg: Term)
Pi(implicit: List(String), name: String, in_term: Term, out_term: Term)
```

**Key Properties**:
1. Implicit args are **erased at runtime** (zero overhead)
2. Implicit args are **filled during type inference**
3. Empty implicit list = backward compatible with existing code

---

## Overloading Design

### Step 1: Define Overloaded Function

In Tao syntax (future):
```tao
fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }
fn (+)(x: F32, y: F32) -> F32 { %f32_add(x, y) }
```

Desugars to Core:
```core
%let (+) = %fn<ty>(args) -> %match ty {
  | {x: %I32, y: %I32} -> %call i32_add(args.x, args.y)
  | {x: %F32, y: %F32} -> %call f32_add(args.x, args.y)
}
```

Core AST:
```gleam
Lam(
  implicit: ["ty"],
  param: #("args", RecordType([("x", Var("ty")), ("y", Var("ty"))])),
  body: Match(Var("ty"), [
    MatchArm(I32T, Call("i32_add", [...]), _),
    MatchArm(F64T, Call("f32_add", [...]), _),
  ], _),
  span,
)
```

---

### Step 2: Use Overloaded Function

In Tao syntax:
```tao
let result = 1 + 2  // I32 version
let float_result = 1.0 + 2.0  // F32 version
```

Desugars to Core (before type inference):
```core
%let result = %call (+)(1, 2)
%let float_result = %call (+)(1.0, 2.0)
```

Core AST (before inference):
```gleam
App(Var("+"), [], Record([("x", Lit(I32(1))), ("y", Lit(I32(2)))]))
```

During type inference:
```
1. (+) has type: ∀ty. {x: ty, y: ty} → ty
2. Arguments have type: {x: I32, y: I32}
3. Unify: ty = I32
4. Result type: I32
5. After inference: App(Var("+"), [I32], Record([...]))
```

---

### Step 3: Evaluation

At runtime, implicit args are erased:

```
App(Var("+"), [I32], Record([...]))
→ Evaluate Var("+") → closure
→ Evaluate Record([...]) → {x: 1, y: 2}
→ Apply closure with implicit arg I32 (erased)
→ Apply closure with explicit arg {x: 1, y: 2}
→ Match on ty = I32
→ %call i32_add(1, 2)
→ 3
```

---

## Implementation Steps

### Phase 1: Update Tao AST (Pending)

Add support for overloaded function definitions:

```gleam
pub type MvpExpr {
  // ... existing
  OverloadedFn(
    name: String,
    overloads: List(Overload),
    span: Span,
  )
}

pub type Overload {
  Overload(
    params: List(#(String, Type)),
    return_type: Type,
    body: MvpExpr,
  )
}
```

---

### Phase 2: Update Desugarer (Pending)

Update `tao/desugar.gleam` to handle overloaded functions:

```gleam
pub fn desugar_overloaded_fn(fn_def) -> Term {
  // Create lambda with implicit type parameter
  Lam(
    implicit: ["ty"],
    param: #("args", record_type),
    body: Match(Var("ty"), match_arms, _),
    span,
  )
}
```

---

### Phase 3: Update Type Inference (Pending)

Ensure type inference instantiates implicit parameters:

```gleam
// In core.gleam infer function
case fun_ty {
  VPi(implicit, name, env, in_val, out_term) => {
    // Create holes for implicit params
    let #(holes, state) = create_holes(implicit, state)
    // Instantiate and continue
  }
}
```

---

### Phase 4: Add Syntax Support (Future)

Add parser support for explicit syntax:

```tao
// Explicit type parameters (future enhancement)
fn id<T>(x: T) -> T { x }
id<I32>(42)

// Implicit (inferred)
id(42)  // T inferred as I32
```

---

## Examples

### Example 1: Unary Negation

```tao
fn (-)(x: I32) -> I32 { %i32_neg(x) }
fn (-)(x: F32) -> F32 { %f32_neg(x) }

let a = -42      // I32
let b = -3.14    // F32
```

---

### Example 2: Vector Addition

```tao
type Vector = Vector(x: F32, y: F32)

fn (+)(v1: Vector, v2: Vector) -> Vector {
  Vector(x: v1.x + v2.x, y: v1.y + v2.y)
}

let v = v1 + v2  // Uses Vector version
```

---

### Example 3: Type Reflection

```tao
fn typeof<T>(x: T) -> Type { T }

let t1 = typeof(42)      // I32
let t2 = typeof("hello") // String
```

---

## Benefits

| Benefit | Description |
|---------|-------------|
| **Zero Overhead** | Implicit args erased at runtime |
| **Type Safety** | Resolved at compile time |
| **Extensible** | Add new overloads without modifying existing code |
| **Composable** | Overloads from different modules can be combined |

---

## Related Documents

- **[10-overloading-design.md](./10-overloading-design.md)** - Full design specification
- **[11-overloading-implementation.md](./11-overloading-implementation.md)** - Implementation plan
- **[16-implicit-arguments-status.md](./16-implicit-arguments-status.md)** - Core implementation status
- **[../../docs/core.md](../../docs/core.md)** - Core language spec

---

**Next Step**: Implement Phase 1 (Tao AST updates) and Phase 2 (Desugarer updates) to enable basic overloading.
