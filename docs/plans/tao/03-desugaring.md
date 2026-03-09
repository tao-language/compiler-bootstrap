# Tao Desugaring Specification

> **Goal**: Define how Tao syntax desugars to core language terms
> **Status**: 📋 Designed
> **Date**: March 2025

---

## Status

### What's Working

- Desugaring rules designed for all Tao constructs
- Type inference strategy specified
- Operator overloading resolution defined
- State threading for mutable variables specified

### What's Pending

- **Desugaring implementation** (`src/tao/desugar.gleam`)
- **Type inference implementation**
- **Operator overloading resolution via NbE**
- **Integration tests** (Tao → Core → Evaluate)

### Related

- See **[01-overview.md](./01-overview.md)** for overall implementation status
- See **[02-syntax.md](./02-syntax.md)** for Tao syntax
- See **[../../docs/core.md](../../docs/core.md)** for core language semantics

---

## Overview

Desugaring converts Tao AST to core language `Term`. The core language handles:
- Type checking (bidirectional)
- Normalization by evaluation
- Exhaustiveness checking
- FFI/comptime evaluation

Tao adds syntax sugar that expands to core constructs.

---

## Variables and Bindings

### Immutable Let

```tao
// Tao
let x = 5
let y: I32 = add(x, 3)

// Core
Ann(Lit(I32(5)), Typ(0))  -- x
Ann(App(App(Var("add"), Var("x")), Lit(I32(3))), Typ(0))  -- y
```

**Desugaring**:
1. Add binding to context
2. Type check RHS
3. Annotate with type (for IDE support)

### Mutable Let

```tao
// Tao
let mut counter = 0
counter = counter + 1
counter = counter * 2

// Core (state threading)
let counter_0 = 0
let counter_1 = add(counter_0, 1)
let counter_2 = mul(counter_1, 2)
-- Use counter_2 from here on
```

**Desugaring**:
1. Generate fresh name for each assignment (`counter_0`, `counter_1`, ...)
2. Thread state explicitly
3. Replace all uses with latest version

**Algorithm**:
```gleam
fn desugar_mutable_let(name, mut assignments) {
  let mut fresh_name = name <> "_0"
  let mut result = []
  
  for (i, assignment) in assignments.enumerate() {
    let current_name = name <> "_" <> i
    let next_name = name <> "_" <> (i + 1)
    
    result.append(desugar_let(current_name, assignment))
    
    -- Replace all uses of 'name' in subsequent code with 'current_name'
    substitute(name, current_name, subsequent_code)
  }
  
  result
}
```

---

## Functions

### Basic Function

```tao
// Tao
fn add(a: I32, b: I32) -> I32 {
  a + b
}

// Core
let add = Lam("a", Lam("b", App(App(Var("+"), Var("a")), Var("b"))))
-- With type annotation
Ann(add, Pi("a", Typ(0), Pi("b", Typ(0), Typ(0))))
```

**Desugaring**:
1. Convert parameters to nested lambdas
2. Type check body
3. Add type annotation

### Generic Function

```tao
// Tao
fn identity(x: a) -> a {
  x
}

// Core (type erased at runtime, explicit in types)
let identity = Lam("x", Var("x"))
-- Type: Pi(a: Type, Pi(x: a, a))
```

**Desugaring**:
1. Type variables become implicit parameters
2. Erased at runtime (NbE handles polymorphism)
3. Type annotation includes quantified variables

### Overloaded Function

```tao
// Tao
fn add(a: I32, b: I32) -> I32 { i32_add(a, b) }
fn add(a: F64, b: F64) -> F64 { f64_add(a, b) }

let x = add(1, 2)      // Resolves to i32_add
let y = add(1.0, 2.0)  // Resolves to f64_add

// Core (type application injected)
let x = App(App(App(Var("add"), Typ(0)), Lit(I32(1))), Lit(I32(2)))
let y = App(App(App(Var("add"), Typ(1)), Lit(F64(1.0))), Lit(F64(2.0)))
```

**Desugaring**:
1. During NbE, inspect argument types
2. Select appropriate overload
3. Inject type application in core Term

**Algorithm**:
```gleam
fn resolve_overload(name, args, ctx) {
  let arg_types = args.map(fn(a) { infer_type(a, ctx) })
  
  case find_matching_overload(name, arg_types, ctx) {
    Ok(overload) => {
      -- Inject type applications
      let type_apps = overload.type_params.map(fn(t) { Typ(t) })
      let arg_apps = args.map(fn(a) { a })
      
      AppN(Var(overload.name), list.append(type_apps, arg_apps))
    }
    Error(_) => {
      -- Error: no matching overload
      record_error(NoMatchingOverload(name, arg_types))
      VErr
    }
  }
}
```

---

## Pattern Matching

### Basic Match

```tao
// Tao
match value {
  Some(x) => x
  None => 0
}

// Core
Match(
  Var("value"),
  Typ(0),  -- motive (return type)
  [
    Case(PCtr("Some", PAs(PAny, "x")), Var("x")),
    Case(PCtr("None", PAny), Lit(I32(0)))
  ]
)
```

**Desugaring**:
1. Convert patterns to core `Pattern`
2. Type check each case body
3. Generate motive (return type)
4. Run exhaustiveness checking

### Match with Guards

```tao
// Tao
match n {
  x if x < 0 => "negative"
  x if x == 0 => "zero"
  x if x > 0 => "positive"
}

// Core (guards become nested if)
Match(
  Var("n"),
  Typ(0),
  [
    Case(
      PAs(PAny, "x"),
      If(
        App(App(Var("<"), Var("x")), Lit(I32(0))),
        Lit(String("negative")),
        Match(
          Var("n"),  -- Continue matching
          Typ(0),
          [
            Case(
              PAs(PAny, "x"),
              If(
                App(App(Var("=="), Var("x")), Lit(I32(0))),
                Lit(String("zero")),
                -- ... and so on
              )
            )
          ]
        )
      )
    )
  ]
)
```

**Desugaring**:
1. Convert guard to `if` expression in case body
2. If guard fails, continue to next case
3. Exhaustiveness checking considers guards

### Record Pattern

```tao
// Tao
let { x, y } = point

// Core (destructuring)
let x = Dot(Var("point"), "x")
let y = Dot(Var("point"), "y")
```

**Desugaring**:
1. Generate field projections
2. Bind each field to variable

---

## Error Handling

### Bind Operator (`<-`)

```tao
// Tao
fn process() -> Result(I32, String) {
  let x <- parse_int("42")
  let y <- parse_int("10")
  Ok(x + y)
}

// Core (expanded to and_then)
let process = Lam("_",
  App(
    App(
      Var("and_then"),
      App(App(Var("parse_int"), Lit(String("42"))))
    ),
    Lam("x",
      App(
        App(
          Var("and_then"),
          App(App(Var("parse_int"), Lit(String("10"))))
        ),
        Lam("y",
          App(App(Var("Ok"), App(App(Var("+"), Var("x")), Var("y"))))
        )
      )
    )
  )
)
```

**Desugaring**:
1. Identify `<-` expressions
2. Convert to chained `and_then` calls
3. Wrap final expression

**Algorithm**:
```gleam
fn desugar_bind(expressions, final_expr, return_type) {
  case expressions {
    [] => final_expr
    [(name, bind_expr), ..rest] => {
      App(
        App(Var("and_then"), bind_expr),
        Lam(name, desugar_bind(rest, final_expr, return_type))
      )
    }
  }
}
```

### Optional Chaining (`?`)

```tao
// Tao (Result)
fn read_config() -> Result(Config, Error) {
  let data = read_file("config.txt")?
  let config = parse_config(data)?
  Ok(config)
}

// Core (expanded to match)
let read_config = Lam("_",
  Match(
    App(App(Var("read_file"), Lit(String("config.txt")))),
    Typ(0),
    [
      Case(
        PCtr("Ok", PAs(PAny, "data")),
        Match(
          App(App(Var("parse_config"), Var("data"))),
          Typ(0),
          [
            Case(
              PCtr("Ok", PAs(PAny, "config")),
              App(Var("Ok"), Var("config"))
            ),
            Case(
              PCtr("Err", PAs(PAny, "e")),
              App(Var("Err"), Var("e"))
            )
          ]
        )
      ),
      Case(
        PCtr("Err", PAs(PAny, "e")),
        App(Var("Err"), Var("e"))
      )
    ]
  )
)
```

**Desugaring**:
1. `?` on Result expands to `match` with early return
2. `Ok` value continues, `Err` returns immediately

### Optional Chaining (`?.`)

```tao
// Tao (Maybe)
let city = user?.address?.city

// Core (expanded to nested match)
let city = Match(
  Var("user"),
  Typ(0),
  [
    Case(
      PCtr("Some", PAs(PAny, "u")),
      Match(
        Dot(Var("u"), "address"),
        Typ(0),
        [
          Case(
            PCtr("Some", PAs(PAny, "addr")),
            Some(Dot(Var("addr"), "city"))
          ),
          Case(PCtr("None", PAny), None)
        ]
      )
    ),
    Case(PCtr("None", PAny), None)
  ]
)
```

**Desugaring**:
1. `?.` on Maybe expands to nested `match`
2. `Some` value continues, `None` short-circuits

---

## Operators

### Operator Desugaring

```tao
// Tao
let x = 1 + 2 * 3

// Core (with precedence)
let x = App(
  App(Var("+"), Lit(I32(1))),
  App(App(Var("*"), Lit(I32(2))), Lit(I32(3)))
)
```

**Desugaring**:
1. Parse with operator precedence
2. Convert to nested applications

### Operator Overloading Resolution

```tao
// Tao
fn add(a: I32, b: I32) -> I32 { ... }
fn add(a: F64, b: F64) -> F64 { ... }

let x = add(1, 2)      -- I32
let y = add(1.0, 2.0)  -- F64

// Core (during NbE)
let x = App(App(App(Var("add"), Typ(0)), Lit(I32(1))), Lit(I32(2)))
let y = App(App(App(Var("add"), Typ(1)), Lit(F64(1.0))), Lit(F64(2.0)))
```

**Resolution Algorithm**:
```gleam
fn resolve_operator(op, args, ctx) {
  -- Get argument types via NbE
  let arg_types = args.map(fn(a) { normalize(eval(a, ctx)) })
  
  -- Find matching overload
  case find_overload(op, arg_types, ctx) {
    Ok(overload) => {
      -- Inject type applications
      inject_type_apps(overload, arg_types, args)
    }
    Error(_) => {
      record_error(AmbiguousOverload(op, arg_types))
      VErr
    }
  }
}
```

---

## Types

### Type Annotation

```tao
// Tao
let x: I32 = 5

// Core
Ann(Lit(I32(5)), LitT(I32T))
```

**Desugaring**:
1. Type check RHS against annotated type
2. Wrap in `Ann` for IDE support

### Generic Type Application

```tao
// Tao
let x: Maybe(I32) = Some(5)

// Core
Ann(
  App(App(Var("Some"), Lit(I32(5)))),
  App(Var("Maybe"), LitT(I32T))
)
```

**Desugaring**:
1. Convert type arguments to core types
2. Apply to type constructor

### Dependent Type

```tao
// Tao
type Vec3 = Vec(3, F64)

// Core
let Vec3 = App(App(Var("Vec"), Lit(I32(3))), LitT(F64T))
```

**Desugaring**:
1. Evaluate type-level expressions
2. Apply to type constructor

---

## Attributes

### Permission Attribute

```tao
// Tao
@permission(Read("/tmp"))
fn read_temp() -> Result(String, Error) {
  read_file("/tmp/data.txt")
}

// Core (metadata in Call/Comptime)
let read_temp = Lam("_",
  Comptime(
    Call("read_file", [Lit(String("/tmp/data.txt"))])
  )
)
-- Permission checked during comptime_eval
```

**Desugaring**:
1. Extract permissions from attributes
2. Check permissions during `comptime_eval`
3. Add to state if allowed

### Effect Attribute

```tao
// Tao
@effect(IO)
fn print(msg: String) -> Unit {
  -- Has side effects
}

// Core (no change, attribute is documentation)
let print = Lam("msg", Call("print", [Var("msg")]))
```

**Desugaring**:
1. Effect attributes are documentation only
2. No runtime change
3. May be used for optimization hints

### Inline Attribute

```tao
// Tao
@inline
fn fast_double(x: I32) -> I32 {
  x * 2
}

// Core (no change, hint for codegen)
let fast_double = Lam("x", App(App(Var("*"), Var("x")), Lit(I32(2))))
```

**Desugaring**:
1. Inline attributes are hints
2. No change to core Term
3. Codegen may inline based on attribute

---

## Comptime

### Comptime Block

```tao
// Tao
comptime {
  let size = 1024
  type Buffer = Array(size, I32)
}

// Core (evaluated during type checking)
let size = comptime_eval(state, Lit(I32(1024)))
let Buffer = App(App(Var("Array"), size), LitT(I32T))
```

**Desugaring**:
1. Evaluate block at compile-time
2. Substitute result in types

### Comptime Function

```tao
// Tao
const fn factorial(n: I32) -> I32 {
  if n <= 1 { 1 } else { n * factorial(n - 1) }
}

let x = factorial(5)

// Core (call evaluated at compile-time)
let factorial = Lam("n", -- ... implementation ...)
let x = comptime_eval(state, App(App(Var("factorial"), Lit(I32(5)))))
-- x = Lit(I32(120))
```

**Desugaring**:
1. Mark function as comptime
2. Evaluate calls at compile-time
3. Substitute result

---

## Type Inference

### Bidirectional Inference

```gleam
-- Infer: term → type
fn infer(s: State, term: TaoAst) -> #(Value, Type, State) {
  case term {
    Var(name) => ctx_get(s.ctx, name)
    App(fun, arg) => {
      let (fun_val, fun_ty, s1) = infer(s, fun)
      let (arg_val, arg_ty, s2) = infer(s1, arg)
      let result_ty = app_ty(fun_ty, arg_ty)
      (App(fun_val, arg_val), result_ty, s2)
    }
    -- ... other cases
  }
}

-- Check: term × type → ()
fn check(s: State, term: TaoAst, expected: Type) -> #(Value, State) {
  case term {
    Lam(name, body) => {
      let (arg_ty, out_ty) = decompose_pi(expected)
      let s1 = extend_ctx(s, name, arg_ty)
      let (body_val, s2) = check(s1, body, out_ty)
      (VLam(name, body_val), s2)
    }
    -- ... other cases
  }
}
```

### Type Injection

```gleam
fn inject_types(s: State, term: TaoAst) -> #(Term, State) {
  case term {
    App(fun, arg) => {
      let (fun_term, s1) = inject_types(s, fun)
      let (arg_term, s2) = inject_types(s1, arg)
      
      -- Inject type application for overloaded functions
      case fun_term {
        Var(name) if is_overloaded(name) => {
          let arg_ty = infer_type(arg_term, s2)
          (App(App(fun_term, type_to_term(arg_ty)), arg_term), s2)
        }
        _ => (App(fun_term, arg_term), s2)
      }
    }
    -- ... other cases
  }
}
```

---

## Error Recovery

### Continue After Errors

```gleam
fn desugar(s: State, term: TaoAst) -> #(Term, State) {
  case term {
    App(fun, arg) => {
      let (fun_term, s1) = desugar(s, fun)
      let (arg_term, s2) = desugar(s1, arg)
      
      case s2.errors {
        [] => (App(fun_term, arg_term), s2)
        _ => (App(fun_term, arg_term), s2)  -- Continue anyway
      }
    }
    -- ... other cases
  }
}
```

### Error Accumulation

```gleam
fn with_err(s: State, err: Error) -> State {
  State(..s, errors: list.append(s.errors, [err]))
}

fn desugar_match(s: State, cases: List(Case)) -> #(List(CoreCase), State) {
  let (core_cases, errors) = list.map_fold(cases, s, fn(s1, c) {
    let (core_case, s2) = desugar_case(s1, c)
    (core_case, s2)
  })
  
  -- Collect all errors from all cases
  let all_errors = list.flat_map(core_cases, fn(c) { c.errors })
  let final_state = list.fold(all_errors, s, with_err)
  
  (core_cases, final_state)
}
```

---

## Implementation Plan

### Phase 1: Basic Desugaring

- [ ] Variables and bindings
- [ ] Functions (no overloading)
- [ ] Basic pattern matching
- [ ] Operators (no overloading)

### Phase 2: Advanced Features

- [ ] Mutable variable state threading
- [ ] Bind operator (`<-`)
- [ ] Optional chaining (`?.`, `?`)
- [ ] Guards in patterns

### Phase 3: Type System

- [ ] Type inference (bidirectional)
- [ ] Type injection
- [ ] Operator overloading resolution
- [ ] Generic functions

### Phase 4: Integration

- [ ] Comptime evaluation
- [ ] Permission checking
- [ ] Error recovery
- [ ] Full round-trip tests

---

## References

- [Tao Overview](./01-overview.md)
- [Tao Syntax](./02-syntax.md)
- [Core Language](../../docs/core.md)
