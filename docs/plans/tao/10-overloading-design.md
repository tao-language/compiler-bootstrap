# Tao Overloading Design (Revised)

> **Goal**: Support function and operator overloading through implicit arguments and NbE
> **Status**: 📋 **Design Phase** - Revised with unified implicit argument approach
> **Date**: March 2026

---

## Core Insight

**Overloading is type-directed instantiation**. Functions can have implicit type parameters that are inferred from context at call sites.

---

## Key Design Decisions

### 1. **Unified Implicit Arguments**

All lambdas and applications support implicit arguments uniformly:

```gleam
// Core Term
Lam(params: List(#(String, Bool, Type)), body: Term)
//               ↑ is_implicit

App(func: Term, args: List(#(Term, Bool)))
//                            ↑ is_implicit
```

**Implicit arguments**:
- Passed during type checking
- Erased at runtime (zero overhead)
- Enable type reflection

---

### 2. **Syntax: `f<ty>(x)`**

Clear distinction between type and value application:

```tao
f(x)       // Normal application (value arg)
f<ty>(x)   // Type application (implicit arg)
f<ty>(x, y) // Mixed: one implicit, two explicit
```

**Core syntax**:
```core
%fn<a>(x) -> body      // Lambda with implicit param
func<ty>(arg)          // Application with implicit arg
```

---

### 3. **Hole-Based Inference**

Tao desugars to normal applications with holes; Core inference fills them:

```tao
// Tao source
(-)(1)

// Desugared (Tao doesn't know types)
(-)(1)  -- Normal App, no implicit info

// During Core inference
(-)<?>(1)  -- Hole created for implicit param
(-)<I32>(1) -- Hole filled based on arg type
```

**Benefit**: Tao desugaring is simple; Core inference handles complexity.

---

### 4. **Polymorphic Types with `Forall`**

Function types encode implicit parameters:

```gleam
// Type of overloaded (-)
Forall(["a"], Fn([Type("a")], Type("a")))  // ∀a. a → a

// Type of non-overloaded function
Fn([I32], I32)  // I32 → I32 (no Forall)
```

**During inference**:
- If function type is `Forall`, instantiate implicit params
- If not, normal application

---

## Complete Example: Unary Negation

### Tao Source

```tao
// Define overloaded negation
fn (-)(x: I32) -> I32 { %i32_neg(x) }
fn (-)(x: F32) -> F32 { %f32_neg(x) }

// Use it
let result = -42
let float_result = -3.14
```

### Desugaring (Tao → Core)

```tao
// Overloaded function becomes type-level match
%let (-) = %fn<ty>(x) -> %match ty {
  | %I32 -> %i32_neg(x)
  | %F32 -> %f32_neg(x)
}

// Usage (Tao doesn't know types yet)
%let result = (-)(42)      -- Normal App
%let float_result = (-)(3.14)
```

### Type Inference (Core)

```
Step 1: Infer type of (-)
  (-) : ∀a. a → a

Step 2: Infer application (-)(42)
  - Function has Forall, create hole for implicit
  - (-)<?>(42)
  - Infer 42 : I32
  - Unify hole with I32
  - Result: (-)<I32>(42) : I32

Step 3: Evaluate
  (-)<I32>(42)
  → %match %I32 { | %I32 -> %i32_neg(42) }
  → %i32_neg(42)
  → -42
```

### Core Terms (After Inference)

```gleam
Let("-",
  Lam(
    [("ty", true, Hole), ("x", false, Var("ty"))],  // ty is implicit
    Match(Var("ty"), [
      MatchArm(I32T, Call(FFI("i32_neg"), [Var("x")], _), _),
      MatchArm(F64T, Call(FFI("f64_neg"), [Var("x")], _), _),
    ], _),
    _
  ),
  Let("result",
    App(Var("-"), [(Lit(I32(42)), false)], _),  // App gets upgraded during infer
    _
  )
)
```

---

## Type Reflection

Implicit arguments enable free type reflection:

```tao
// Get type of any value
fn typeof<T>(x: T) -> Type { T }

typeof(42)      // I32
typeof("hello") // String
typeof([1,2,3]) // List<I32>
```

**Desugars to**:
```core
%let typeof = %fn<T>(x) -> T

typeof<?> (42)   // Hole created
typeof<I32>(42)  // Hole filled
// Returns: %I32
```

---

## Overload Resolution

### Multiple Overloads

```tao
fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }
fn (+)(x: F32, y: F32) -> F32 { %f32_add(x, y) }
fn (+)(v1: Vector, v2: Vector) -> Vector { ... }
```

**Core representation**:
```core
%let (+) = %fn<ty>(args) -> %match ty {
  | {x: %I32, y: %I32} -> %call i32_add(args.x, args.y)
  | {x: %F64, y: %F64} -> %call f64_add(args.x, args.y)
  | {v1: Vector, v2: Vector} -> ...
}
```

### Resolution Process

```
1. Parse: (+)(1, 2)

2. Infer args: 1 : I32, 2 : I32

3. Check function type: (+) : ∀a. {x: a, y: a} → a

4. Instantiate: (+)<?>({x: 1, y: 2})

5. Unify: {x: ?, y: ?} with {x: I32, y: I32}
   → ? = I32

6. Result: (+)<I32>({x: 1, y: 2}) : I32
```

---

## Cross-Module Overloads

```tao
// prelude.tao
export fn (+)(x: I32, y: I32) -> I32 { ... }
export fn (+)(x: F32, y: F32) -> F32 { ... }

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
  | {x: %I32, y: %I32} -> ...  // From prelude
  | {x: %F64, y: %F64} -> ...  // From prelude
  | {v1: Vector, v2: Vector} -> ...  // From vector
}
```

---

## Implementation Architecture

### Core Changes

```gleam
// src/core/core.gleam

pub type Term {
  // ... existing
  Var(index: Int, span: Span)
  
  // Unified Lam with implicit params
  Lam(
    params: List(#(String, Bool, Term)),  // name, is_implicit, type_annotation
    body: Term,
    span: Span,
  )
  
  // Unified App with implicit args
  App(
    func: Term,
    args: List(#(Term, Bool)),  // term, is_implicit
    span: Span,
  )
  
  // ... rest unchanged
}

pub type Type {
  // ... existing
  Var(String)
  Fn(List(Type), Type)
  
  // Polymorphic type
  Forall(List(String), Type)  // ∀a. a → a
}
```

### Inference Changes

```gleam
// src/core/core.gleam (infer function)

pub fn infer(state, term) -> #(InferResult, State) {
  case term {
    App(func, args, span) => {
      let #(func_result, state1) = infer(state, func)
      
      case func_result.typ {
        Forall(params, body_ty) => {
          // Function has implicit params - instantiate them
          let #(holes, state2) = create_holes(params, state1)
          let instantiated = substitute(func_result.term, params, holes)
          apply(instantiated, args, body_ty, span, state2)
        }
        _ => {
          // Normal application
          apply(func_result.term, args, func_result.typ, span, state1)
        }
      }
    }
    
    // ... rest unchanged
  }
}
```

### Evaluation Changes

```gleam
// src/core/core.gleam (eval function)

pub fn eval(ffi, env, term) -> Value {
  case term {
    App(func, args, span) => {
      // Separate implicit and explicit args
      let implicit_args = list.filter_map(args, fn(#(arg, is_implicit)) {
        case is_implicit {
          True -> Some(eval(ffi, env, arg))  // Evaluate but erase
          False -> None
        }
      })
      let explicit_args = list.filter_map(args, fn(#(arg, is_implicit)) {
        case is_implicit {
          True -> None
          False -> Some(eval(ffi, env, arg))
        }
      })
      
      let func_val = eval(ffi, env, func)
      
      case func_val {
        VLam(params, body, closure_env) => {
          // Match implicit params with implicit args
          // Extend environment and evaluate body
        }
      }
    }
    
    // ... rest unchanged
  }
}
```

**Key**: Implicit args are evaluated (for side effects) but erased from runtime representation.

---

## Desugaring Pipeline

```
Tao Source
    ↓
[Parse]
    ↓
Tao AST
    ↓
[Desugar]  -- Desugar to normal App (no implicit info)
    ↓
Core Term (pre-inference)
    ↓
[Type Infer] -- Upgrade to implicit App, fill holes
    ↓
Core Term (post-inference)
    ↓
[Evaluate] -- Erase implicit args
    ↓
Value
```

---

## Open Questions & Decisions

### Q1: How to handle match arms with implicit args?

**Answer**: Each arm can bind implicit params:

```core
%match ty ~ motive {
  | %I32 -> %fn<a = I32>(x) -> %i32_neg(x)
  | %F64 -> %fn<a = F64>(x) -> %f64_neg(x)
}
```

Arm type includes implicit param binding.

---

### Q2: Can implicit params have defaults?

**Answer**: Future extension:

```tao
fn id<T = I32>(x: T) -> T { x }
id(42)  // Uses default I32 if context doesn't specify
```

**Decision**: Not in MVP, add later if needed.

---

### Q3: How to handle higher-order functions with implicit params?

```tao
fn map<T, U>(f: fn(T) -> U, xs: List<T>) -> List<U> { ... }
map((-), [1, 2, 3])  // What type for (-)?
```

**Answer**: Contextual inference:

```
1. xs : List<I32>, so T = I32
2. f : fn(I32) -> U
3. (-) : ∀a. a → a
4. Instantiate (-) with a = I32
5. Result: map<I32, I32>((-)<I32>, [1, 2, 3])
```

---

### Q4: What about implicit params in records/ADTs?

**Answer**: Same mechanism:

```tao
type Box<T> = Box(value: T)

fn unwrap<T>(box: Box<T>) -> T { box.value }

unwrap(Box(42))  // T inferred as I32
```

**Core**:
```core
Box : ∀a. a → Box<a>
unwrap : ∀a. Box<a> → a
```

---

## Benefits of This Design

| Benefit | Description |
|---------|-------------|
| **Simplicity** | Single Lam/App, not multiple constructors |
| **Uniformity** | All functions use same mechanism |
| **Type Reflection** | Free from implicit argument mechanism |
| **Zero Overhead** | Implicit args erased at runtime |
| **Hole Inference** | Leverages existing infrastructure |
| **Consistency** | Matches Pi types at type level |
| **Extensibility** | Easy to add more implicit param kinds |

---

## Comparison with Alternatives

| Approach | Pros | Cons |
|----------|------|------|
| **Explicit Type App** `f(T)(x)` | Simple | Verbose, no inference |
| **Implicit Args** `f<ty>(x)` | Inferred, clean syntax | More complex inference |
| **Type Classes** | Powerful | Complex, runtime dictionaries |
| **Multi-Dispatch** | Flexible | Runtime overhead |

**Decision**: Implicit args provide best balance of simplicity and power.

---

## Related Documents

- **[11-overloading-implementation.md](./11-overloading-implementation.md)** - Implementation plan (needs update)
- **[../core/15-type-application.md](../core/15-type-application.md)** - Core type application (superseded by this)
- **[09-tao-mvp-plan.md](./09-tao-mvp-plan.md)** - Tao MVP (completed)

---

## Next Steps

1. **Update Core AST** - Add implicit flag to Lam/App
2. **Add Forall to Type** - Polymorphic type support
3. **Update Inference** - Instantiate Forall, fill holes
4. **Update Evaluation** - Erase implicit args
5. **Update Formatter** - Print `<ty>` syntax
6. **Tests** - Verify overloading, type reflection

---

**This design unifies implicit arguments, overloading, and type reflection elegantly.** 🎯
