# Tao Overloading Design (v3)

> **Goal**: Support function and operator overloading through implicit arguments and NbE
> **Status**: 📋 **Design Phase** - v3 with single explicit argument
> **Date**: March 2026

---

## Core Insight

**Overloading is type-directed instantiation with recursive implicit handling**. Functions have implicit type parameters inferred from context, with a single explicit argument (record or curried for multi-param).

---

## Key Design Decisions

### 1. **Single Explicit Argument**

```gleam
pub type Term {
  // ... existing
  
  // Single explicit param (name + type)
  Lam(
    implicit: List(String),
    param: #(String, Type),
    body: Term,
    span: Span,
  )
  
  // Single explicit arg (recursive implicit handling)
  App(
    func: Term,
    implicit: List(Term),
    arg: Term,
    span: Span,
  )
  
  // ... rest unchanged
}
```

**Benefits**:
- ✅ Single base case: `App(func, [], arg)`
- ✅ Recursive implicit handling
- ✅ Multi-arg via records or currying
- ✅ Matches lambda calculus

---

### 2. **Multi-Arg Strategies**

#### Option A: Record Argument (Recommended for Overloading)

```tao
// Tao
fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }

// Core (single record arg)
Lam(
  implicit: ["ty"],
  param: #("args", RecordType([("x", Var("ty")), ("y", Var("ty"))])),
  body: Match(Var("ty"), [
    MatchArm(I32T, Call(FFI("i32_add"), [Field(Var("args"), "x"), Field(Var("args"), "y")], _), _),
  ], _),
  span,
)

// Application
App(Var("+"), [Hole], Record([("x", Lit(I32(1))), ("y", Lit(I32(2)))]))
```

**Benefits**:
- Single argument (matches design)
- Clean pattern matching on record fields
- Named fields for clarity

---

#### Option B: Curried Lambdas

```tao
// Tao (curried)
fn add(x: I32) -> fn(y: I32) -> I32 { x + y }

// Core (nested Lambdas)
Lam(
  implicit: [],
  param: #("x", I32),
  body: Lam(
    implicit: [],
    param: #("y", I32),
    body: Call(FFI("i32_add"), [Var("x"), Var("y")], _),
    span2,
  ),
  span1,
)

// Application (nested Apps)
App(App(Var("add"), [], Lit(I32(1))), [], Lit(I32(2)))
```

**Benefits**:
- No record syntax needed
- Supports partial application
- Matches lambda calculus

---

### 3. **Recursive Implicit Handling**

```gleam
pub fn eval(ffi: Ffi, env: Env, term: Term) -> Value {
  case term {
    App(func, [], arg, span) => {
      // BASE CASE: No implicit args
      // Apply function to single argument
      let func_val = eval(ffi, env, func)
      let arg_val = eval(ffi, env, arg)
      
      case func_val {
        VLam(implicit, param_name, body, closure_env) => {
          let extended_env = extend_env(closure_env, [param_name], [arg_val])
          eval(ffi, extended_env, body)
        }
        _ => Error(RuntimeError("Not a function"))
      }
    }
    
    App(func, [implicit, ..rest], arg, span) => {
      // RECURSIVE CASE: Peel off one implicit arg
      let implicit_val = eval(ffi, env, implicit)  // Evaluate but erase
      let func_val = eval(ffi, env, func)
      
      case func_val {
        VLam(implicit_params, param_name, body, closure_env) => {
          // Instantiate function with implicit, recurse
          let instantiated = instantiate(func_val, implicit_val)
          eval(ffi, env, App(instantiated, rest, arg, span))
        }
      }
    }
    
    Lam(implicit, param, body, span) => {
      VLam(implicit, param, body, env)
    }
    
    // ... rest unchanged
  }
}
```

**Key Insight**: Recursive case peels off implicit args until base case (empty implicit).

---

### 4. **Hole-Based Inference**

```gleam
pub fn infer(state: State, term: Term) -> #(InferResult, State) {
  case term {
    App(func, implicit, arg, span) => {
      let #(func_result, state1) = infer(state, func)
      let #(arg_result, state2) = infer(state1, arg)
      
      case func_result.typ {
        Forall(params, body_ty) => {
          // Function has implicit params - instantiate them
          let #(holes, state3) = create_holes(params, state2)
          let instantiated_term = substitute(func_result.term, params, holes)
          let instantiated_ty = substitute_type(body_ty, params, holes)
          
          // Recurse with instantiated function
          infer(state3, App(instantiated_term, implicit, arg, span))
        }
        
        Fn(param_ty, return_ty) => {
          // Base case: check arg matches param type
          case unify(arg_result.typ, param_ty, state2) {
            Ok(state4) => #(InferResult(return_ty, span), state4)
            Error(e) => #(InferResult(Error(e), span), state2)
          }
        }
      }
    }
    
    // ... rest unchanged
  }
}
```

---

## Complete Examples

### Example 1: Unary Negation (Single Arg)

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
  param: #("x", Var("ty")),
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
  arg: Lit(I32(42)),
  span,
)
```

**Inference**:
```
1. (-) : ∀a. a → a
2. App((-), <?>, 42)
3. Infer 42 : I32
4. Unify ? = I32
5. Result: App((-), <I32>, 42) : I32
```

---

### Example 2: Addition (Record Arg)

```tao
// Tao source
fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }

let result = 1 + 2
```

**Core AST**:
```gleam
// Overloaded function with record arg
Lam(
  implicit: ["ty"],
  param: #("args", RecordType([("x", Var("ty")), ("y", Var("ty"))])),
  body: Match(Var("ty"), [
    MatchArm(
      I32T,
      Call(FFI("i32_add"), [Field(Var("args"), "x"), Field(Var("args"), "y")], _),
      _,
    ),
  ], _),
  span,
)

// Application: (+)(1, 2)
App(
  func: Var("+"),
  implicit: [Hole],  // Filled with I32
  arg: Record([("x", Lit(I32(1))), ("y", Lit(I32(2)))]),
  span,
)
```

---

### Example 3: Curried Function

```tao
// Tao (curried)
fn add(x: I32) -> fn(y: I32) -> I32 { x + y }

let result = add(1)(2)
```

**Core AST**:
```gleam
// Curried function (nested Lambdas)
Lam(
  implicit: [],
  param: #("x", I32),
  body: Lam(
    implicit: [],
    param: #("y", I32),
    body: Call(FFI("i32_add"), [Var("x"), Var("y")], _),
    span2,
  ),
  span1,
)

// Application (nested Apps)
App(
  App(Var("add"), [], Lit(I32(1))),
  [],
  Lit(I32(2)),
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
  param: #("x", Var("T")),
  body: Var("T"),
  span,
)

// Application: typeof(42)
App(
  func: Var("typeof"),
  implicit: [Hole],  // Filled with I32
  arg: Lit(I32(42)),
  span,
)

// Result: %I32 (type value)
```

---

## Evaluation Trace

```
// Term: App(Var("-"), [I32], Lit(42))

eval(App(Var("-"), [I32], Lit(42))) {
  // Recursive case: implicit not empty
  eval(App(instantiated_minus, [], Lit(42))) {
    // Base case: implicit empty
    apply(instantiated_minus, 42) {
      // Match on record/param
      eval(body with x = 42)
      → %i32_neg(42)
      → -42
    }
  }
}
```

---

## Benefits of This Design

| Benefit | Description |
|---------|-------------|
| **Single Base Case** | `App(func, [], arg)` - same as current |
| **Recursive Handling** | Peel off implicit args one by one |
| **Clean Evaluation** | Simple recursion, no list zipping |
| **Record or Curried** | Flexible multi-arg support |
| **Type Reflection** | Free from implicit argument mechanism |
| **Zero Overhead** | Implicit args erased at runtime |
| **Hole Inference** | Leverages existing infrastructure |

---

## Comparison with Alternatives

| Design | Pros | Cons |
|--------|------|------|
| **Multiple Explicit Args** `args: List(Term)` | Direct multi-arg | Complex pattern matching |
| **Single Explicit Arg** `arg: Term` | Clean, recursive | Need records/currying for multi-arg |
| **Mixed Flags** `args: List(#(Term, Bool))` | Flexible | Confusing flags |

**Decision**: Single explicit arg provides cleanest implementation.

---

## Syntax

```tao
// Single arg (no implicit)
fn double(x: I32) -> I32 { x * 2 }

// Single arg with implicit (overloaded)
fn (-)<ty>(x: ty) -> ty { ... }

// Record arg (multi-param)
fn (+)<ty>(args: {x: ty, y: ty}) -> ty { ... }

// Curried (multi-param)
fn add(x: I32) -> fn(y: I32) -> I32 { x + y }

// Type application syntax
f<T>(x)      // One implicit, one explicit
f<T, U>(x)   // Multiple implicit, one explicit
```

---

## Related Documents

- **[11-overloading-implementation.md](./11-overloading-implementation.md)** - Implementation plan (v3)
- **[../core/15-type-application.md](../core/15-type-application.md)** - Superseded
- **[09-tao-mvp-plan.md](./09-tao-mvp-plan.md)** - Tao MVP (completed)

---

**This design with single explicit argument provides the cleanest recursive implementation.** 🎯
