# Operator Overloading Design

## Design Philosophy

1. **Literal overloading** — Integer and float literals resolve to concrete types during type inference (handled in Core, see 03-core-language.md)
2. **Function overloading via pattern matching** — Same name with different types resolved by pattern matching on implicit parameters (application argument types)
3. **FFI calls single targets** — FFI entries call one concrete target function with no overloads (`%i32_add`, `%f32_add`, etc.)
4. **Operator desugaring** — Operators are just functions with special names and syntax sugar for precedence. Calling them and their overloads is treated just as regular functions.
5. **No runtime overhead** — All overloading is resolved by NbE at compile time since most types are known at compile time
6. **No methods** — There are no methods in this language, only functions and operators. Binary functions use `infix` notation, and `|>` pipe is available.
7. **Dependent types** — Different definitions can return different types, so overloading tests dependent types.

## Literal Overloading

### Type System

See 03-core-language.md for the full `LitType` definition. The key types are:

```gleam
/// Literal type — concrete during type checking, generic during inference
pub type LitType {
  // Concrete types — specific bit-width and signedness
  I32T   // 32-bit signed integer
  I64T   // 64-bit signed integer
  U32T   // 32-bit unsigned integer
  U64T   // 64-bit unsigned integer
  F32T   // 32-bit float
  F64T   // 64-bit float
  
  // Generic types — used during inference when type is not yet resolved
  ILitT  // Generic integer literal type (unifies with I32T, I64T, U32T, U64T)
  FLitT  // Generic float literal type (unifies with F32T, F64T)
}
```

### Unification Rules

```gleam
/// Unify two literal types — returns State (success) or State with error (failure)
fn unify_literal_type(expected: LitType, actual: LitType) -> State {
  case expected, actual {
    // Concrete matches concrete
    (_, concrete) when is_concrete(concrete) -> State // Already unified
    
    // Integer literal type matches any concrete integer type
    (ILitT, I32T) | (ILitT, I64T) | (ILitT, U32T) | (ILitT, U64T) -> State
    // Float literal type matches any concrete float type
    (FLitT, F32T) | (FLitT, F64T) -> State
    
    // Concrete integer type matches integer literal type
    (I32T, ILitT) | (I64T, ILitT) | (U32T, ILitT) | (U64T, ILitT) -> State
    // Concrete float type matches float literal type
    (F32T, FLitT) | (F64T, FLitT) -> State
    
    // FAIL: integer and float literal types are incompatible
    (ILitT, FLitT) -> State // Error: cannot unify integer with float
    (FLitT, ILitT) -> State // Error: cannot unify float with integer
  }
}
```

### Example: Integer Literal Resolution

```gleam
// Tao source
let x: Int = 42

// Desugars to Core
let x = Lit(ILit(42))  // ILit(42) is an untyped integer literal

// Type checking
// 1. Infer type of Lit(ILit(42)) → ILitT (overloaded integer)
// 2. Check against annotation Int (which is I32T)
// 3. Unify(ILitT, I32T) → ILitT resolved to I32T
// 4. Result: x has type I32T
```

### Example: Float Literal Resolution

```gleam
// Tao source
let x: Float = 3.14

// Desugars to Core
let x = Lit(FLit(3.14))  // FLit(3.14) is an untyped float literal

// Type checking
// 1. Infer type of Lit(FLit(3.14)) → FLitT (overloaded float)
// 2. Check against annotation Float (which is F64T)
// 3. Unify(FLitT, F64T) → FLitT resolved to F64T
// 4. Result: x has type F64T
```

## Function Overloading

### Core Principle: Pattern Matching on Implicit Parameters

Function overloading is handled through **pattern matching**, not FFI resolution. A Tao function with multiple type signatures desugars to a function that first pattern matches on the implicit parameter (the application argument types), then branches to the appropriate definition.

`Lam` can receive implicit parameters — this is how the overloading is encoded in the Core language.

### FFI: Single Target Functions

FFI entries call one concrete target function with **no overloads**:

```gleam
/// FFI builtin definition
pub type FfiEntry {
  FfiEntry(
    name: String,
    impl: fn(List(#(Value, Value))) -> Option(Value),  // (value, type) pairs
    ret_type: Value,  // Return type
  )
}
```

FFI receives **both the argument values and their types** as `List(#(Value, Value))`. Each FFI entry is a single concrete target — there are no overloaded FFI entries.

Example FFI entries for addition:
```gleam
FfiEntry(name: "%i32_add", impl: int_add_impl, ret_type: I32T)
FfiEntry(name: "%f32_add", impl: float_add_impl, ret_type: F32T)
FfiEntry(name: "%i64_add", impl: int64_add_impl, ret_type: I64T)
```

### Desugaring: Overloaded Function → Pattern Match

An overloaded function like:

```tao
fn add(Int, Int) -> Int { a + b }
fn add(Float, Float) -> Float { a + b }
```

desugars to a Core term that pattern matches on the implicit application argument type:

```gleam
/// The overloaded "add" desugars to:
let add = \(implicit_args) ->
  match implicit_args {
    | #(I32T, I32T) -> %i32_add
    | #(I64T, I64T) -> %i64_add
    | #(F32T, F32T) -> %f32_add
    | #(F64T, F64T) -> %f64_add
  }
```

This is a single function that returns different function values depending on the implicit parameter type. NbE resolves the match at compile time.

### Different Return Types: Dependent Types

Different definitions can return different types. For example:

```tao
fn concat(String, String) -> String { /* string concat */ }
fn concat(List(a), List(a)) -> List(a) { /* list append */ }
```

This tests dependent types — the return type depends on the argument types. The pattern match on implicit args determines both the branch and the return type.

## Operator Desugaring

### Operators Are Just Functions

Operators are just functions with special names and syntax sugar for precedence. Calling them and overloads is treated just as regular functions.

The operator `(+)` desugars to a function called `"+"` which pattern matches on the argument types and branches to `%i32_add`, `%f32_add`, etc. The operator syntax is purely syntactic sugar — behind the scenes it's a regular function call with an overloaded name.

### Operator Resolution Table

| Operator | Desugars To | FFI Names (overloaded) |
|----------|-------------|----------------------|
| `+` | `+(a, b)` | `%i32_add`, `%i64_add`, `%f32_add`, `%f64_add` |
| `-` | `- (a, b)` | `%i32_sub`, `%i64_sub`, `%f32_sub`, `%f64_sub` |
| `*` | `* (a, b)` | `%i32_mul`, `%i64_mul`, `%f32_mul`, `%f64_mul` |
| `/` | `/ (a, b)` | `%i32_div`, `%i64_div`, `%f32_div`, `%f64_div` |
| `%` | `mod(a, b)` | `%i32_mod`, `%i64_mod`, `%f32_mod`, `%f64_mod` |
| `==` | `== (a, b)` | `%eq` (polymorphic) |
| `!=` | `!= (a, b)` | `%neq` (polymorphic) |
| `<` | `< (a, b)` | `%i32_lt`, `%i64_lt`, `%f32_lt`, `%f64_lt` |
| `>` | `> (a, b)` | `%i32_gt`, `%i64_gt`, `%f32_gt`, `%f64_gt` |
| `<=` | `<= (a, b)` | `%i32_lte`, `%i64_lte`, `%f32_lte`, `%f64_lte` |
| `>=` | `>= (a, b)` | `%i32_gte`, `%i64_gte`, `%f32_gte`, `%f64_gte` |
| `&&` | `and(a, b)` | `%bool_and` |
| `\|\|` | `or(a, b)` | `%bool_or` |
| `.` | `dot(record, field)` | `%dot` (record field access) |
| `|>` | `pipe(x, f)` | `%pipe` |
| `<>` | `<> (a, b)` | `%concat` (polymorphic append) |

### Unary Operators

| Operator | Desugars To | FFI Names |
|----------|-------------|----------|
| `-x` | `negate(x)` | `%i32_neg`, `%i64_neg`, `%f32_neg`, `%f64_neg` |
| `!x` | `not(x)` | `%bool_not` |

### Example: Operator Overloading Resolution

```gleam
// Tao source
let x = 1 + 2

// Desugars to Core — the "+" function pattern matches on argument types
let x = App("+", [Lit(ILit(1)), Lit(ILit(2))])

// Type checking
// 1. Infer type of Lit(ILit(1)) → ILitT
// 2. Infer type of Lit(ILit(2)) → ILitT
// 3. "+" desugars to: \implicit -> match implicit { #(ILitT,ILitT) -> %i32_add }
// 4. NbE resolves the match to %i32_add
// 5. Call(%i32_add, [I32(1), I32(2)]) → I32(3)
// 6. Result: x has type I32 with value 3
```

## Note: No Methods

There are no methods in this language — only functions and operators. Binary functions use `infix` notation and there's `|>` pipe. Constructors are handled by the type checker looking them up in the constructor environment (CtrEnv), not as methods. See 03-core-language.md for constructor resolution details.

## Test Cases

### Literal Overloading Tests

```gleam
should("resolve integer literal to I32") {
  let state = initial_state([])
  let result = check(state, Lit(ILit(42)), I32T)
  case result {
    #(term, I32T, State(errors: [], ctrs: _)) -> True  // Unification succeeds
    _ -> False
  }
}

should("resolve integer literal to U64") {
  let state = initial_state([])
  let result = check(state, Lit(ILit(42)), U64T)
  case result {
    #(term, U64T, State(errors: [], ctrs: _)) -> True  // ILitT unifies with U64T
    _ -> False
  }
}

should("reject float literal as integer type") {
  let state = initial_state([])
  let result = check(state, Lit(FLit(3.14)), I32T)
  case result {
    #(term, _, State(errors: [TypeMismatch(_, _, _, _)], _)) -> True  // FLitT cannot unify with I32T
    _ -> False
  }
}

should("resolve 1 + 2 to I32 when both args are integer literals") {
  let state = initial_state([])
  let plus = Lam(("implicit", App("%i32_add", [Var(1, span), Var(0, span)]), span))  // overloaded + pattern matches on implicit
  let term = App(plus, [Lit(ILit(1)), Lit(ILit(2))])
  let result = infer(state, term)
  case result {
    #(term, I32T, State(errors: [], ctrs: _)) -> True  // NbE resolves to I32 + I32 → I32
    _ -> False
  }
}

should("resolve 1.0 + 2.0 to F64 when both args are float literals") {
  let state = initial_state([])
  // Similar test for float
  let result = infer(state, App(plus, [Lit(FLit(1.0)), Lit(FLit(2.0))]))
  case result {
    #(term, F64T, State(errors: [], ctrs: _)) -> True  // NbE resolves to F64 + F64 → F64
    _ -> False
  }
}
```

### Function Overloading (Pattern Match) Tests

```gleam
should("resolve add via pattern match when both args are I32") {
  let state = initial_state([])
  // "+" desugars to: \implicit -> match implicit { #(I32T,I32T) -> %i32_add }
  let plus = Lam(("implicit", Match(Var(0, span), [
    Case(PCtr(2, [PTyp(I32T), PTyp(I32T)], span), Hole(1, span), None, span),
  ]), span))
  let result = infer(state, App(plus, [Lit(ILit(1)), Lit(ILit(2))]))
  case result {
    #(term, I32T, State(errors: [], ctrs: _)) -> True  // Pattern match resolves to %i32_add
    _ -> False
  }
}

should("resolve add via pattern match when both args are F64") {
  let state = initial_state([])
  // Similar for F64
  let result = infer(state, App(plus, [Lit(FLit(1.0)), Lit(FLit(2.0))]))
  case result {
    #(term, F64T, State(errors: [], ctrs: _)) -> True  // Pattern match resolves to %f64_add
    _ -> False
  }
}

should("fail add(Int, Float) — no matching pattern") {
  let state = initial_state([])
  let result = infer(state, App(plus, [Lit(ILit(1)), Lit(FLit(2.0))]))
  case result {
    #(term, _, State(errors: [MatchMissingCase(_, _, _)], _)) -> True  // No matching branch
    _ -> False
  }
}
```

### Constructor Tests

```gleam
should("resolve Some(42) to Option(I32)") {
  let state = initial_state([("Some", CtrDef([], Hole(-1), Ctr("Option", Hole(-1), Span)))])
  let result = infer(state, Ctr("Some", Lit(ILit(42))))
  case result {
    #(term, CtrValue("Option", ...), State(errors: [], ctrs: _)) -> True
    _ -> False
  }
}

should("fail undefined constructor") {
  let state = initial_state([])
  let result = infer(state, Ctr("Undefined", Lit(ILit(42))))
  case result {
    #(term, _, State(errors: [CtrUndefined("Undefined", _)], _)) -> True
    _ -> False
  }
}
```
