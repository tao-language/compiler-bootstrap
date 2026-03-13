# Core Type Application Support

> **Goal**: Add type application to Core for Tao overloading support
> **Status**: 📋 **Planned** - Prerequisite for Tao overloading
> **Priority**: High (blocks Tao Phase 2)

---

## Motivation

Tao will support function and operator overloading through type-directed dispatch:

```tao
// Tao source
fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }
fn (+)(x: F32, y: F32) -> F32 { %f32_add(x, y) }

let result = 1 + 2  // Resolves to I32 version
```

This requires Core to support **type application**:

```core
// Core target
%let (+) = λ(ty: Type) → match ty {
  | {x: %I32, y: %I32} → λ(args) → %call i32_add(args.x, args.y)
  | {x: %F32, y: %F32} → λ(args) → %call f32_add(args.x, args.y)
}

%let result = %call (%call (+)(%I32))(1, 2)
```

---

## Changes Required

### 1. Term: Type Application

**File**: `src/core/core.gleam`

```gleam
pub type Term {
  // ... existing constructors
  Var(index: Int, span: Span)
  Lam(name: String, body: Term, span: Span)
  Call(func: Term, args: List(Term), span: Span)
  // ...
  
  // NEW: Type application
  TypeApp(term: Term, types: List(Type), span: Span)
}
```

**Semantics**:
- `TypeApp(f, [T1, T2], span)` applies type arguments to a term
- Types are erased at runtime (only used for type checking)
- Multiple type args: `TypeApp(f, [T1, T2], span)` = `TypeApp(TypeApp(f, [T1], span), [T2], span)`

---

### 2. Evaluation

**File**: `src/core/core.gleam` (eval function)

```gleam
pub fn eval(ffi: Ffi, env: Env, term: Term) -> Value {
  case term {
    // ... existing cases
    
    TypeApp(func, _types, _span) -> {
      // Type application is erased at runtime
      // Just evaluate the function
      eval(ffi, env, func)
    }
    
    // ...
  }
}
```

**Key Insight**: Types are compile-time only. At runtime, `TypeApp(f, T)` is just `f`.

---

### 3. Type Checking

**File**: `src/core/core.gleam` (infer function)

```gleam
pub fn infer(state: State, term: Term) -> #(InferResult, State) {
  case term {
    // ... existing cases
    
    TypeApp(func, types, span) -> {
      // Infer type of the function
      let #(func_result, state1) = infer(state, func)
      
      // Check that the function accepts these type arguments
      // For now, just verify types are well-formed
      // In the future, may need to check against function's type scheme
      
      // The result type is the function's return type with types substituted
      // For MVP, just return the function's type
      let result = InferResult(
        term: TypeApp(func_result.term, types, span),
        typ: substitute_types(func_result.typ, types),
      )
      
      #(result, state1)
    }
    
    // ...
  }
}
```

**Notes**:
- Type substitution may be needed for polymorphic functions
- For MVP, can skip full polymorphism and just check well-formedness

---

### 4. Formatting

**File**: `src/core/syntax.gleam`

```gleam
pub fn format(term: Term) -> String {
  case term {
    // ... existing cases
    
    TypeApp(func, types, _span) -> {
      format(func) <> "(" <> string_join(list.map(types, format_type), ", ") <> ")"
    }
    
    // ...
  }
}

fn format_type(typ: Type) -> String {
  case typ {
    I32T -> "%I32"
    F64T -> "%F64"
    // ...
  }
}
```

---

### 5. Parsing (Optional)

For testing, may want to parse Core terms with type application:

```core
// Example syntax
f(T1, T2)(arg1, arg2)  // Type application then value application
```

**File**: `src/core/syntax.gleam` (grammar)

```gleam
// Extend grammar to parse TypeApp
rule("Primary", [
  // ...
  alt(seq([
    ref("Atom"),
    many(seq([
      token_pattern("LParen"),
      ref("TypeOrExpr"),  // Could be type or expr
      token_pattern("RParen"),
    ])),
  ]), make_app),
])

fn make_app(values) -> Term {
  case values {
    [func_ast, ListValue(apps)] -> {
      let func = ast_to_term(func_ast)
      list.fold(apps, func, fn(acc, app_val) -> {
        case app_val {
          [type_ast, _] -> {
            // Check if it's a type or expression
            case is_type(type_ast) {
              True -> TypeApp(acc, [ast_to_type(type_ast)], span)
              False -> Call(acc, [ast_to_term(type_ast)], span)
            }
          }
        }
      })
    }
  }
}
```

---

## Examples

### Example 1: Polymorphic Identity

```core
// Source
%let id = λ(ty: Type) → λ(x: ty) → x

// Usage
id(%I32)(42)  // Type application then value application
id(%F64)(3.14)
```

```gleam
// Core AST
Let("id", 
  Lam("ty", 
    Lam("x", Var(0), span1), 
    span2
  ), 
  span3
)

// Usage
Call(
  TypeApp(Var("id"), [%I32], span),
  [Lit(I32(42))],
  span
)
```

### Example 2: Overloaded Addition

```core
// Source
%let (+) = λ(ty: Type) → match ty {
  | {x: %I32, y: %I32} → λ(args) → %call i32_add(args.x, args.y)
  | {x: %F64, y: %F64} → λ(args) → %call f64_add(args.x, args.y)
}

%let result = %call (%call (+)(%I32))(1, 2)
```

```gleam
// Core AST for usage
Call(
  Call(
    TypeApp(Var("+"), [%I32], span),
    [Lit(I32(1)), Lit(I32(2))],
    span1
  ),
  [],
  span2
)
```

---

## Implementation Phases

### Phase 1: Data Structure (Day 1-2)

- [ ] Add `TypeApp` constructor to `Term`
- [ ] Update all pattern matches (use compiler errors as guide)
- [ ] Basic tests for creating TypeApp

### Phase 2: Evaluation (Day 3)

- [ ] Add TypeApp case to `eval`
- [ ] Tests: TypeApp evaluates to function
- [ ] Tests: Type args are erased

### Phase 3: Type Checking (Day 4)

- [ ] Add TypeApp case to `infer`
- [ ] Type substitution for polymorphic functions
- [ ] Tests: TypeApp type checks correctly

### Phase 4: Formatting (Day 5)

- [ ] Add TypeApp case to `format`
- [ ] Tests: Format TypeApp correctly
- [ ] Round-trip tests

---

## Test Plan

### Unit Tests

```gleam
// test/core/core_test.gleam
pub fn type_app_create_test() {
  let term = TypeApp(Var(0), [%I32], span)
  term |> should.not_be_nil()
}

// test/core/eval_test.gleam
pub fn type_app_eval_test() {
  // λ(ty) → λ(x) → x applied to %I32 and 42
  let term = Call(
    TypeApp(Lam("ty", Lam("x", Var(0), s1), s2), [%I32], s3),
    [Lit(I32(42))],
    s4
  )
  eval(term) |> should.equal(VLit(I32(42)))
}

// test/core/infer_test.gleam
pub fn type_app_infer_test() {
  let term = TypeApp(Var("id"), [%I32], span)
  let #(_result, state) = infer(initial_state, term)
  state.errors |> should.equal([])
}

// test/core/syntax_test.gleam
pub fn type_app_format_test() {
  let term = TypeApp(Var("f"), [%I32, %F64], span)
  format(term) |> should.equal("f(%I32, %F64)")
}
```

### Integration Tests

```gleam
// test/core/type_app_integration_test.gleam
pub fn polymorphic_identity_test() {
  let source = "%let id = λ(ty: Type) → λ(x: ty) → x in id(%I32)(42)"
  run(source) |> should.equal(42)
}

pub fn overloaded_add_simulation_test() {
  // Simulate overloaded + using type application
  let source = "
    %let add = λ(ty) → match ty {
      | {x: %I32, y: %I32} → λ(args) → %call i32_add(args.x, args.y)
    }
    %call (%call add(%I32))(1, 2)
  "
  run(source) |> should.equal(3)
}
```

---

## Compatibility

### Backward Compatibility

- Existing Core programs continue to work
- TypeApp is a new constructor, doesn't affect existing terms
- Type erasure means no runtime overhead for existing code

### Forward Compatibility

- Enables Tao overloading
- Enables polymorphic functions in Core
- Foundation for dependent types

---

## Performance Considerations

### Compile Time

- Type checking may be slower due to type substitution
- Mitigation: Cache substitution results

### Runtime

- **Zero overhead**: Types are erased
- `TypeApp(f, T)` evaluates to same value as `f`

---

## Future Extensions

### 1. Polymorphic Types

```gleam
pub type Type {
  // ... existing
  TVar(String)  // Type variable
  Forall(List(String), Type)  // Polymorphic type
}
```

### 2. Type Inference

```gleam
// Infer type arguments from context
// f(42, 3.14) could infer f: (I32, F64) → a
```

### 3. Type Constraints

```core
// Constrain type parameters
%let f = λ(ty: Num) → ...  // ty must be a numeric type
```

---

## Related Documents

- **[../tao/10-overloading-design.md](../tao/10-overloading-design.md)** - Tao overloading design
- **[../tao/11-overloading-implementation.md](../tao/11-overloading-implementation.md)** - Tao implementation plan
- **[01-overview.md](./01-overview.md)** - Core overview
- **[../../docs/core.md](../../docs/core.md)** - Core specification

---

## Success Criteria

Type application is complete when:

- ✅ `TypeApp` constructor added to `Term`
- ✅ Evaluation erases types correctly
- ✅ Type checking handles type applications
- ✅ Formatting produces readable output
- ✅ 20+ tests passing
- ✅ Polymorphic identity example works
- ✅ Overloaded addition simulation works

---

**This is a foundational feature for Tao overloading. Keep it simple and correct.** 🎯
