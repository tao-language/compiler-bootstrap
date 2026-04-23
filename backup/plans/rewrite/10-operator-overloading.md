# Operator Overloading Design

## Design Philosophy

1. **Literal overloading** — Integer and float literals resolve to concrete types during type inference
2. **Function overloading** — Same name, different types (resolved by unification)
3. **Operator desugaring** — Operators become function calls (no special compiler handling)
4. **No runtime overhead** — All overloading is resolved at compile time

## Literal Overloading

### Type System

```gleam
/// Resolved literal type (concrete)
pub type LiteralType {
  I32T  // 32-bit signed integer
  I64T  // 64-bit signed integer
  U32T  // 32-bit unsigned integer
  U64T  // 64-bit unsigned integer
  F32T  // 32-bit float
  F64T  // 64-bit float
}

/// Overloaded literal type (during inference)
/// ILitT unifies with any integer LiteralType
/// FLitT unifies with any float LiteralType
pub type LiteralType {
  ILitT  // Overloaded integer literal type
  FLitT  // Overloaded float literal type
}
```

### Unification Rules

```gleam
/// Unify two literal types
fn unify_literal_type(expected: LiteralType, actual: LiteralType) -> State {
  case expected, actual {
    // Concrete matches concrete
    (_, concrete) when is_concrete(concrete) -> State // Already unified
    
    // Overloaded matches any concrete
    (ILitT, I32T) | (ILitT, I64T) | (ILitT, U32T) | (ILitT, U64T) -> State
    (ILitT, FLitT) -> State
    (FLitT, F32T) | (FLitT, F64T) -> State
    
    // Concrete matches overloaded
    (I32T, ILitT) | (I64T, ILitT) | (U32T, ILitT) | (U64T, ILitT) -> State
    (I32T, FLitT) | (F64T, FLitT) -> State
    
    // Overloaded matches overloaded (unresolved — wait for context)
    (ILitT, FLitT) -> State
    (FLitT, ILitT) -> State
  }
}
```

### Example: Integer Literal Resolution

```gleam
// Tao source
let x: Int = 42

// Desugars to Core
let x = Lit(I32(42))  // I32(42) is an untyped literal

// Type checking
// 1. Infer type of Lit(I32(42)) → ILitT (overloaded integer)
// 2. Check against annotation Int (which is I32T)
// 3. Unify(ILitT, I32T) → ILitT resolved to I32T
// 4. Result: x has type I32T
```

### Example: Float Literal Resolution

```gleam
// Tao source
let x: Float = 3.14

// Desugars to Core
let x = Lit(F64(3.14))  // F64(3.14) is an untyped literal

// Type checking
// 1. Infer type of Lit(F64(3.14)) → FLitT (overloaded float)
// 2. Check against annotation Float (which is F64T)
// 3. Unify(FLitT, F64T) → FLitT resolved to F64T
// 4. Result: x has type F64T
```

## Function Overloading

### FFI-Based Overloading

```gleam
/// Function overloading is achieved through FFI entries
/// Each FFI entry has a name, implementation, argument types, and return type
pub type FfiEntry {
  FfiEntry(
    name: String,              // Function name (e.g., "add")
    impl: fn(List(Value)) -> Option(Value),  // Implementation
    arg_types: List(Value),    // Expected argument types
    ret_type: Value,           // Return type
  )
}
```

### Resolution Process

```gleam
/// Resolve a function call by trying each FFI entry in order
fn resolve_call(state: State, name: String, args: List(Value)) -> State {
  // Get all FFI entries for this name
  let entries = list.filter(state.ffi, fn(entry) -> entry.name == name)
  
  // Try each entry in order
  try_entry(state, entries, 0, args)
}

/// Try a specific FFI entry
fn try_entry(state: State, entries: List(FfiEntry), index: Int, args: List(Value)) -> State {
  case list.get(entries, index) {
    Ok(entry) -> {
      // Try to unify args with entry.arg_types
      let unified_state = unify_list(state, args, entry.arg_types)
      
      case has_unsolved_holes(unified_state) {
        True -> try_entry(unified_state, entries, index + 1, args)  // Try next entry
        False -> unified_state  // Found a match
      }
    }
    Error(_) -> state  // No more entries to try
  }
}
```

### Example: Add Function Overloading

```gleam
// FFI entries for "add"
let add_entries = [
  FfiEntry(
    name: "add",
    impl: fn(args) -> int_add(args),
    arg_types: [I32T, I32T],
    ret_type: I32T,
  ),
  FfiEntry(
    name: "add",
    impl: fn(args) -> int64_add(args),
    arg_types: [I64T, I64T],
    ret_type: I64T,
  ),
  FfiEntry(
    name: "add",
    impl: fn(args) -> float_add(args),
    arg_types: [F64T, F64T],
    ret_type: F64T,
  ),
]

// Tao source
fn add_i32(a: Int, b: Int) -> Int { a + b }
fn add_f64(a: Float, b: Float) -> Float { a + b }
fn add_mixed(a: Int, b: Float) -> Float { a + b }  // Error: types don't match any entry
```

## Operator Desugaring

### Tao Operator → Core Function Call

All operators are desugared to Core function calls. This means:

1. **Operators are just functions** — `+` is the same as `add`
2. **No special compiler handling** — Operators go through the same FFI resolution
3. **Type inference works the same** — Operator types are resolved like any other function

### Operator Resolution Table

| Operator | Desugars To | FFI Name |
|----------|-------------|----------|
| `+` | `add(a, b)` | `"add"` |
| `-` | `sub(a, b)` | `"sub"` |
| `*` | `mul(a, b)` | `"mul"` |
| `/` | `div(a, b)` | `"div"` |
| `%` | `mod(a, b)` | `"mod"` |
| `==` | `eq(a, b)` | `"eq"` |
| `!=` | `neq(a, b)` | `"neq"` |
| `<` | `lt(a, b)` | `"lt"` |
| `>` | `gt(a, b)` | `"gt"` |
| `<=` | `lte(a, b)` | `"lte"` |
| `>=` | `gte(a, b)` | `"gte"` |
| `&&` | `and(a, b)` | `"and"` |
| `\|\|` | `or(a, b)` | `"or"` |
| `.` | `dot(record, field)` | `"dot"` (record field access) |
| `|>` | `pipe(x, f)` | `"pipe"` |
| `<>` | `concat(a, b)` | `"concat"` |

### Unary Operators

| Operator | Desugars To | FFI Name |
|----------|-------------|----------|
| `-x` | `negate(x)` | `"negate"` |
| `!x` | `not(x)` | `"not"` |

### Example: Operator Type Resolution

```gleam
// Tao source
let x = 1 + 2

// Desugars to Core
let x = Call("add", [Lit(I32(1)), Lit(I32(2))], Hole(-1))

// Type checking
// 1. Infer type of Lit(I32(1)) → ILitT
// 2. Infer type of Lit(I32(2)) → ILitT
// 3. Look up FFI entries for "add"
// 4. Try [I32T, I32T] → ILitT unifies with I32T ✓
// 5. Result: Call("add", [Lit(I32(1)), Lit(I32(2))], I32T)
```

## Method Overloading (ADT Constructors)

### Constructor Resolution

```gleam
/// Constructor resolution during type checking
/// Constructors are looked up in the constructor environment (CtrEnv)
fn resolve_constructor(state: State, name: String) -> State {
  case list.find(state.ctrs, fn(#(ctor_name, _)) -> ctor_name == name) {
    Ok((name, CtrDef(_, arg_ty, ret_ty))) -> {
      // Constructor found, create term with resolved type
      Ok(TermCtrRef(name, arg_ty, ret_ty))
    }
    Error(_) -> Error(CtrUndefined(name, state))
  }
}
```

### Example: Constructor Resolution

```gleam
// Tao source
type Option(a) = Some(a) | None

let x: Option(Int) = Some(42)

// Desugars to Core
let x = Ctr("Some", Lit(I32(42)))

// Type checking
// 1. Infer type of Lit(I32(42)) → ILitT
// 2. Look up constructor "Some" in CtrEnv
// 3. "Some" has type Πa. a → Option(a)
// 4. Unify(ILitT, a) → a = I32T
// 5. Result: Ctr("Some", Lit(I32(42))) has type Option(I32T)
```

## Test Cases for Operator Overloading

### Literal Overloading Tests

```gleam
should("resolve integer literal to I32") {
  let state = initial_state([], tao_ffis(), "True", "False")
  let result = check(state, Lit(I32(42)), I32T)
  case result {
    State(errors: [], ctrs: _) -> True  // Unification succeeds
    _ -> False
  }
}

should("resolve float literal to F64") {
  let state = initial_state([], tao_ffis(), "True", "False")
  let result = check(state, Lit(F64(3.14)), F64T)
  case result {
    State(errors: [], ctrs: _) -> True
    _ -> False
  }
}

should("allow mixed literal and concrete types") {
  let state = initial_state([], tao_ffis(), "True", "False")
  let result = check(state, Lit(I32(42)), I64T)  // I32 literal against I64 type
  case result {
    State(errors: [], ctrs: _) -> True  // ILitT unifies with I64T
    _ -> False
  }
}

should("resolve add(42, 1) to I32 when both args are integer literals") {
  let state = initial_state([], tao_ffis(), "True", "False")
  let add_term = Call("add", [Lit(I32(42)), Lit(I32(1))], Hole(-1))
  let result = infer(state, add_term)
  case result {
    State(errors: [], ctrs: _) -> True  // Resolves to I32 + I32 → I32
    _ -> False
  }
}

should("resolve add(1.0, 2.0) to F64 when both args are float literals") {
  let state = initial_state([], tao_ffis(), "True", "False")
  let add_term = Call("add", [Lit(F64(1.0)), Lit(F64(2.0))], Hole(-1))
  let result = infer(state, add_term)
  case result {
    State(errors: [], ctrs: _) -> True  // Resolves to F64 + F64 → F64
    _ -> False
  }
}
```

### Function Overloading Tests

```gleam
should("resolve add(Int, Int) when both args are I32") {
  let state = initial_state([], tao_ffis(), "True", "False")
  let add_term = Call("add", [Lit(I32(1)), Lit(I32(2))], Hole(-1))
  let result = infer(state, add_term)
  case result {
    State(errors: [], ctrs: _) -> True  // Matches [I32T, I32T] → I32T
    _ -> False
  }
}

should("resolve add(Float, Float) when both args are F64") {
  let state = initial_state([], tao_ffis(), "True", "False")
  let add_term = Call("add", [Lit(F64(1.0)), Lit(F64(2.0))], Hole(-1))
  let result = infer(state, add_term)
  case result {
    State(errors: [], ctrs: _) -> True  // Matches [F64T, F64T] → F64T
    _ -> False
  }
}

should("fail add(Int, Float) — no matching entry") {
  let state = initial_state([], tao_ffis(), "True", "False")
  let add_term = Call("add", [Lit(I32(1)), Lit(F64(2.0))], Hole(-1))
  let result = infer(state, add_term)
  case result {
    State(errors: [TypeMismatch(_, _, _, _)], _) -> True  // No matching FFI entry
    _ -> False
  }
}
```

### Constructor Resolution Tests

```gleam
should("resolve Some(42) to Option(I32)") {
  let state = initial_state([("Some", CtrDef([], Hole(-1), Ctr("Option", Hole(-1), Span)))], tao_ffis(), "True", "False")
  let result = infer(state, Ctr("Some", Lit(I32(42))))
  case result {
    State(errors: [], ctrs: _) -> True
    _ -> False
  }
}

should("fail undefined constructor") {
  let state = initial_state([], tao_ffis(), "True", "False")
  let result = infer(state, Ctr("Undefined", Lit(I32(42))))
  case result {
    State(errors: [CtrUndefined("Undefined", _)], _) -> True
    _ -> False
  }
}
```
