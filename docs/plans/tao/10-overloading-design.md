# Tao Overloading Design (v2)

> **Goal**: Support function and operator overloading through implicit arguments and NbE
> **Status**: 📋 **Design Phase** - v2 with separated implicit/explicit parameters
> **Date**: March 2026

---

## Core Insight

**Overloading is type-directed instantiation**. Functions have implicit type parameters inferred from context, with a clean separation between implicit and explicit arguments.

---

## Key Design Decisions

### 1. **Separated Implicit/Explicit Parameters**

```gleam
pub type Term {
  // ... existing
  
  Lam(
    implicit: List(String),           // Type params: <a, b>
    params: List(#(String, Type)),    // Value params: (x: I32, y: I32)
    body: Term,
    span: Span,
  )
  
  App(
    func: Term,
    implicit: List(Term),             // Type args: <I32, F32>
    args: List(Term),                 // Value args: (1, 2)
    span: Span,
  )
  
  // ... rest unchanged
}
```

**Benefits**:
- ✅ Clear separation (no mixed flags)
- ✅ Implicit always first: `f<a, b>(x, y)`
- ✅ Multiple explicit params supported
- ✅ Both lists can be empty

---

### 2. **Syntax: `f<ty>(x)`**

```tao
f(x)         // Normal application
f<ty>(x)     // Type application (implicit arg)
f<a, b>(x, y) // Multiple implicit and explicit
```

**Core syntax**:
```core
%fn<a>(x) -> body      // Lambda with implicit param
func<ty>(arg)          // Application with implicit arg
```

---

### 3. **Hole-Based Inference**

Tao desugars to normal applications; Core inference fills implicit holes:

```tao
// Tao source
(-)(1)

// Desugared (normal App, no implicit info)
App(Var("-"), [], [Lit(I32(1))])

// During Core inference
App(Var("-"), [Hole], [Lit(I32(1))])  -- Hole created
App(Var("-"), [%I32], [Lit(I32(1))])  -- Hole filled
```

**Benefit**: Tao desugaring is simple; Core inference handles complexity.

---

### 4. **Polymorphic Types with `Forall`**

```gleam
pub type Type {
  // ... existing
  Var(String)
  Fn(List(Type), Type)
  
  // Polymorphic type (for implicit params)
  Forall(List(String), Type)  // ∀a. a → a
}
```

**During inference**:
- If function type is `Forall`, instantiate implicit params
- If not, normal application

---

## Complete Examples

### Example 1: Unary Negation

```tao
// Tao source
fn (-)(x: I32) -> I32 { %i32_neg(x) }
fn (-)(x: F32) -> F32 { %f32_neg(x) }

let result = -42
```

**Core AST**:
```gleam
// Overloaded function
Lam(
  implicit: ["ty"],
  params: [#("x", Var("ty"))],
  body: Match(Var("ty"), [
    MatchArm(I32T, Call(FFI("i32_neg"), [Var("x")], _), _),
    MatchArm(F64T, Call(FFI("f64_neg"), [Var("x")], _), _),
  ], _),
  span,
)

// Application: (-)(42)
App(
  func: Var("-"),
  implicit: [Hole],  // Filled with I32 during inference
  args: [Lit(I32(42))],
  span,
)
```

**Inference**:
```
1. (-) : ∀a. a → a
2. App((-), <?>, [42])
3. Infer 42 : I32
4. Unify ? = I32
5. Result: App((-), <I32>, [42]) : I32
```

---

### Example 2: Overloaded Addition (Record Arg)

```tao
// Tao source
fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }
fn (+)(x: F32, y: F32) -> F32 { %f32_add(x, y) }

let result = 1 + 2
```

**Core AST**:
```gleam
// Overloaded function with record arg
Lam(
  implicit: ["ty"],
  params: [#("args", RecordType([("x", Var("ty")), ("y", Var("ty"))]))],
  body: Match(Var("ty"), [
    MatchArm(
      I32T,
      Call(FFI("i32_add"), [Field(Var("args"), "x"), Field(Var("args"), "y")], _),
      _,
    ),
    MatchArm(
      F64T,
      Call(FFI("f64_add"), [Field(Var("args"), "x"), Field(Var("args"), "y")], _),
      _,
    ),
  ], _),
  span,
)

// Application: (+)(1, 2)
App(
  func: Var("+"),
  implicit: [Hole],  // Filled with I32
  args: [Record([("x", Lit(I32(1))), ("y", Lit(I32(2)))] )],
  span,
)
```

---

### Example 3: Regular Function (No Implicit)

```tao
// Tao source
fn double(x: I32) -> I32 { x * 2 }

let result = double(5)
```

**Core AST**:
```gleam
// Regular function (no implicit params)
Lam(
  implicit: [],
  params: [#("x", I32)],
  body: Call(FFI("i32_mul"), [Var("x"), Lit(I32(2))], _),
  span,
)

// Application: double(5)
App(
  func: Var("double"),
  implicit: [],  // No implicit args
  args: [Lit(I32(5))],
  span,
)
```

---

### Example 4: Type Reflection

```tao
// Tao source
fn typeof<T>(x: T) -> Type { T }

let t = typeof(42)  // I32
```

**Core AST**:
```gleam
// typeof function
Lam(
  implicit: ["T"],
  params: [#("x", Var("T"))],
  body: Var("T"),
  span,
)

// Application: typeof(42)
App(
  func: Var("typeof"),
  implicit: [Hole],  // Filled with I32
  args: [Lit(I32(42))],
  span,
)

// Result: %I32 (type value)
```

---

## Inference Algorithm

```gleam
pub fn infer(state: State, term: Term) -> #(InferResult, State) {
  case term {
    App(func, implicit_args, explicit_args, span) => {
      let #(func_result, state1) = infer(state, func)
      
      case func_result.typ {
        Forall(params, body_ty) => {
          // Function has implicit params - instantiate them
          let #(holes, state2) = create_holes(params, state1)
          let instantiated_term = substitute(func_result.term, params, holes)
          let instantiated_ty = substitute_type(body_ty, params, holes)
          
          // Apply with explicit args
          apply(instantiated_term, explicit_args, instantiated_ty, span, state2)
        }
        
        _ => {
          // Normal application (no Forall)
          apply(func_result.term, explicit_args, func_result.typ, span, state1)
        }
      }
    }
    
    // ... rest unchanged
  }
}
```

---

## Evaluation with Erasure

```gleam
pub fn eval(ffi: Ffi, env: Env, term: Term) -> Value {
  case term {
    App(func, implicit_args, explicit_args, span) => {
      // Evaluate implicit args (for side effects) but erase
      let _implicit_vals = list.map(implicit_args, fn(arg) { eval(ffi, env, arg) })
      
      // Evaluate explicit args
      let explicit_vals = list.map(explicit_args, fn(arg) { eval(ffi, env, arg) })
      
      let func_val = eval(ffi, env, func)
      
      case func_val {
        VLam(implicit_params, params, body, closure_env) => {
          // Extend environment with explicit args only
          // Implicit args are erased at runtime
          let extended_env = extend_env(closure_env, params, explicit_vals)
          eval(ffi, extended_env, body)
        }
      }
    }
    
    Lam(implicit, params, body, span) => {
      VLam(implicit, params, body, env)
    }
    
    // ... rest unchanged
  }
}
```

**Key**: Implicit args evaluated but **erased** from runtime environment.

---

## Desugaring Pipeline

```
Tao Source
    ↓
[Parse]
    ↓
Tao AST
    ↓
[Desugar]  -- Desugar to App with empty implicit list
    ↓
Core Term (pre-inference): App(func, [], [args])
    ↓
[Type Infer] -- Upgrade to implicit App, fill holes
    ↓
Core Term (post-inference): App(func, [I32], [args])
    ↓
[Evaluate] -- Erase implicit args
    ↓
Value
```

---

## Cross-Module Overloads

```tao
// prelude.tao
export fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }
export fn (+)(x: F32, y: F32) -> F32 { %f32_add(x, y) }

// vector.tao
import prelude

type Vector = Vector(x: F32, y: F32)

export fn (+)(v1: Vector, v2: Vector) -> Vector {
  Vector(
    x: v1.x + v2.x,  // Uses prelude's + for F32
    y: v1.y + v2.y,
  )
}
```

**Core merges overload sets**:
```core
// Combined (+) in Core
%let (+) = %fn<ty>(args) -> %match ty {
  | {x: %I32, y: %I32} -> %call i32_add(args.x, args.y)  // From prelude
  | {x: %F64, y: %F64} -> %call f64_add(args.x, args.y)  // From prelude
  | {v1: Vector, v2: Vector} -> ...  // From vector
}
```

---

## Benefits of This Design

| Benefit | Description |
|---------|-------------|
| **Clean Separation** | Implicit and explicit params are separate lists |
| **No Mixed Flags** | No `is_implicit` boolean per param |
| **Implicit First** | Consistent ordering: `f<a>(x)` |
| **Multiple Explicit** | Supports multi-param functions naturally |
| **Type Reflection** | Free from implicit argument mechanism |
| **Zero Overhead** | Implicit args erased at runtime |
| **Hole Inference** | Leverages existing infrastructure |

---

## Comparison with Alternatives

| Design | Pros | Cons |
|--------|------|------|
| **Mixed Flags** `List(#(String, Bool, Type))` | Flexible | Confusing, error-prone |
| **Separated Lists** `implicit: List, params: List` | Clear, clean | Slightly more fields |
| **Single Explicit Only** | Simplest | Forces currying/records |

**Decision**: Separated lists provide best balance of clarity and flexibility.

---

## Open Questions

### Q1: Should implicit list always be non-empty for overloaded functions?

**Answer**: Convention, not enforced. Regular functions have `implicit: []`.

---

### Q2: Can explicit params be empty?

**Answer**: Technically yes (type-level function), but rare in practice.

```tao
// Type-level function (no value params)
fn type_id<T>() -> Type { T }
```

**Core**:
```gleam
Lam(
  implicit: ["T"],
  params: [],  // No value params
  body: Var("T"),
  span,
)
```

---

### Q3: How to handle match arms with implicit params?

**Answer**: Each arm binds implicit params locally:

```core
%match ty ~ motive {
  | %I32 -> %fn<a = I32>(x) -> %i32_neg(x)
  | %F64 -> %fn<a = F64>(x) -> %f64_neg(x)
}
```

---

## Related Documents

- **[11-overloading-implementation.md](./11-overloading-implementation.md)** - Implementation plan
- **[../core/15-type-application.md](../core/15-type-application.md)** - Superseded
- **[09-tao-mvp-plan.md](./09-tao-mvp-plan.md)** - Tao MVP (completed)

---

**This design provides clean separation of implicit and explicit parameters with minimal complexity.** 🎯
