# Desugaring Reference: High-Level Features → Core

This document provides a detailed reference for how every Tao high-level feature desugars to Core terms.

## General Principles

1. **Everything desugars to Core** — No high-level features survive into type checking
2. **Desugaring is purely syntactic** — No type checking or evaluation during desugaring
3. **Desugaring preserves semantics** — The desugared term has the same meaning as the original
4. **Desugaring produces valid Core** — Every desugared term is a well-formed Core term

## Lambda Abstraction

### Tao Source
```tao
fn(x: a) -> a { x }
```

### Desugared Core
```gleam
Lam(("x", Hole(-1)), Var(0, "x"))
```

### Multiple Parameters (Curried)
```tao
// Tao
fn add(a: Int, b: Int) -> Int { a + b }

// Desugared Core
Lam(("a", I32T), Lam(("b", I32T), App(App(Var("add"), Var(1, "a")), Var(0, "b"))))
```

## Function Definition

### Tao Source
```tao
fn add(a, b) { a + b }
```

### Desugared Core
```gleam
Let("add", Lam(("a", Hole(-1)), Lam(("b", Hole(-1)), App(App(Var("add"), Var(1, "a")), Var(0, "b")))), Hole(-1))
```

The function body is wrapped in nested lambdas. The function name is bound to this lambda via `Let`.

## Let Binding

### Tao Source
```tao
let x = 42
```

### Desugared Core
```gleam
Let("x", Lit(ILit(42)), Hole(-1))
```

### Multiple Let Bindings (Sequential)
```tao
// Tao
let x = 42
let y = x + 1
y
```

### Desugared Core
```gleam
Let("x", Lit(ILit(42)), Let("y", App(App(Var("+"), Var(1, "x")), Lit(ILit(1))), Var(0, "y")))
```

## Pattern Matching

### Match Expression
```tao
// Tao
match x {
  | Some(y) -> y
  | None -> 0
}
```

### Desugared Core
```gleam
Match(
  Var(0, "x"),
  Hole(-1),  // motive (inferred)
  [
    Case(PCtr("Some", PVar("y")), Var(0, "y"), None),
    Case(PCtr("None", Unit()), Lit(ILit(0)), None),
  ],
)
```

### Match with Guard
```tao
// Tao
match x {
  | Some(y) if y > 0 -> y
  | _ -> 0
}
```

### Desugared Core
```gleam
Match(
  Var(0, "x"),
  Hole(-1),
  [
    Case(PCtr("Some", PVar("y")), Var(0, "y"), Some(App(App(Var(">"), Var(0, "y")), Lit(ILit(0))))),
    Case(PAny(), Lit(ILit(0)), None),
  ],
)
```

## If-Else Expression

### Tao Source
```tao
if cond { a } else { b }
```

### Desugared Core
```gleam
Match(
  Var(0, "cond"),
  Hole(-1),
  [
    Case(PCtr("True", PAny()), Var(0, "a"), None),
    Case(PCtr("False", PAny()), Var(0, "b"), None),
  ],
)
```

**Note:** The `else` branch is optional:
```tao
if cond { a }
```
Desugars to:
```gleam
Match(
  Var(0, "cond"),
  Hole(-1),
  [
    Case(PCtr("True", PAny()), Var(0, "a"), None),
    // No False case — type error if cond is Bool
  ],
)
```

## For Loop

### Tao Source
```tao
for x in [1, 2, 3] {
  print(x)
}
```

### Desugared Core
```gleam
Let("iter", Call("iterator", [List([Lit(ILit(1)), Lit(ILit(2)), Lit(ILit(3))])]),
Let("loop", Fix("loop",
  Match(Call("next", Var(0, "iter")),
    Hole(-1),
    [
      Case(PCtr("Some", PVar("x")),
        App(Call("print", [Var(0, "x")])),
        App(Var(1, "loop"), Unit())),
      Case(PCtr("None", Unit()), Unit(), None),
    ],
  ),
),
Var(0, "loop"))
```

**Key insight:** `for` desugars to a `fix` expression (recursive lambda) that iterates over an iterator.

## While Loop

### Tao Source
```tao
while x > 0 {
  x = x - 1
}
```

### Desugared Core
```gleam
Let("loop", Fix("loop",
  Match(App(App(Var(">"), Var(0, "x")), Lit(ILit(0))),
    Hole(-1),
    [
      Case(PCtr("True", PAny()),
        App(Call("=", Var(0, "x"), App(App(Var("-"), Var(0, "x")), Lit(ILit(1))))),
        App(Var(1, "loop"), Unit())),
      Case(PCtr("False", PAny()), Unit(), None),
    ],
  ),
))
```

## Loop (Infinite)

### Tao Source
```tao
loop {
  print("hello")
}
```

### Desugared Core
```gleam
Fix("loop", App(Call("print", [String("hello")]), App(Var(0, "loop"), Unit())))
```

## Break and Continue

### Tao Source
```tao
for x in [1, 2, 3, 4, 5] {
  if x == 3 { break }
  print(x)
}
```

### Desugared Core
```gleam
Let("iter", Call("iterator", [List([Lit(ILit(1)), Lit(ILit(2)), Lit(ILit(3)), Lit(ILit(4)), Lit(ILit(5))])]),
Let("loop", Fix("loop",
  Match(Call("next", Var(0, "iter")),
    Hole(-1),
    [
      Case(PCtr("Some", PVar("x")),
        Match(App(App(Var("=="), Var(0, "x")), Lit(ILit(3))),
          Hole(-1),
          [
            Case(PCtr("True", PAny()), Call("break", [Var(2, "loop"), Unit()]), None),
            Case(PCtr("False", PAny()),
              App(Call("print", [Var(0, "x")])),
              App(Var(1, "loop"), Unit())),
          ],
        ),
      Case(PCtr("None", Unit()), Unit(), None),
    ],
  ),
)),
Var(0, "loop"))
```

**Key insight:** `break` and `continue` are desugared to FFI calls that interact with the loop's fixpoint:
- `break` → `call_break(loop, value)` — exits the loop with an optional value
- `continue` → `call_continue(loop, value)` — continues the loop with the next iteration

## Yield (Generators)

### Tao Source
```tao
type Stream(a) = Cons(head: a, tail: Stream(a)) | Empty

fn range(start, end) {
  if start >= end {
    Stream.empty()
  } else {
    yield start
    range(start + 1, end)
  }
}
```

### Desugared Core
```gleam
Let("range", Lam(("start", Hole(-1)), Lam(("end", Hole(-1)),
  Match(App(App(Var(">="), Var(1, "start")), Var(0, "end")),
    Hole(-1),
    [
      Case(PCtr("True", PAny()), Call("Stream.empty", [])),
      Case(PCtr("False", PAny()),
        App(App(Call("Stream.cons", [Var(1, "start")])), App(Var(2, "range"), App(App(Var("+"), Var(1, "start")), Lit(ILit(1))), Var(0, "end")))),
      None),
    ],
  ),
)),
```

**Key insight:** `yield` desugars to `Stream.cons(yielded_value, range(...))`. The `yield` keyword is transformed into a cons cell construction.

## Mutable Variables

### Tao Source
```tao
mut counter = 0
counter = counter + 1
counter = counter + 1
```

### Desugared Core
```gleam
Let("counter_0", Lit(ILit(0)),
Let("counter_1", App(App(Var("+"), Var(0, "counter_0")), Lit(ILit(1))),
Let("counter_2", App(App(Var("+"), Var(0, "counter_1")), Lit(ILit(1))),
Var(0, "counter_2"))))
```

**Key insight:** Each "mutation" creates a new immutable binding with a unique name. The desugarer tracks variable names and generates unique names (counter_0, counter_1, counter_2, etc.).

## Record Update

### Tao Source
```tao
{ ..person, age: 30 }
```

### Desugared Core
```gleam
Let("_old", Var(0, "person"),
Let("age", Lit(ILit(30)),
Rcd([
  #("name", Dot("_old", "name")),
  #("age", Var(0, "age")),
])))
```

**Key insight:** Record update desugars to record construction with explicit field access for unchanged fields.

## Pipe Operator

### Tao Source
```tao
1 |> (\x -> x + 1) |> (\x -> x * 2)
```

### Desugared Core
```gleam
App(App(Call("*"), App(Call("+"), Lit(ILit(1)), Lit(ILit(1)))), Lit(ILit(2)))
```

**Key insight:** `x |> f` desugars to `f(x)`. Pipe operators are right-associative.

## Result Bind (Monadic)

### Tao Source
```tao
let x <- result_a
let y <- result_b
x + y
```

### Desugared Core
```gleam
Match(Var(0, "result_a"),
  Hole(-1),
  [
    Case(PCtr("Some", PVar("x")),
      Match(Var(1, "result_b"),
        Hole(-1),
        [
          Case(PCtr("Some", PVar("y")), Var(0, "x"), None),
          Case(PCtr("None", PAny()), Call("error", ["result_b failed"]), None),
        ],
      ),
    None),
    Case(PCtr("None", PAny()), Call("error", ["result_a failed"]), None),
  ],
)
```

**Key insight:** Result bind desugars to nested pattern matches with error handling.

## Comptime Block

### Tao Source
```tao
comptime {
  let x = 42
  x + 1
}
```

### Desugared Core
```gleam
Comptime(
  Let("x", Lit(ILit(42)), App(App(Var("+"), Var(0, "x")), Lit(ILit(1)))),
)
```

**Key insight:** `comptime` is a Core term wrapper. The evaluator treats `Comptime(term)` specially — it evaluates `term` at compile time and replaces it with the result.

## Run Statement

### Tao Source
```tao
run 42 + 1
```

### Desugared Core
```gleam
Call("run", [App(App(Var("+"), Lit(ILit(42))), Lit(ILit(1)))], Hole(-1))
```

**Key insight:** `run` is an FFI builtin that prints the evaluated result.

## Test Statement

### Tao Source
```tao
test "addition" {
  1 + 1 == 2
}
```

### Desugared Core
```gleam
Call("test", [String("addition"), App(App(Var("=="), App(App(Var("+"), Lit(ILit(1)), Lit(ILit(1)))), Lit(ILit(2)))]), Hole(-1))
```

**Key insight:** `test` is an FFI builtin that runs the body and reports pass/fail.

## Summary Table

| Tao Feature | Desugars To | Core Term |
|-------------|-------------|-----------|
| `fn f(x) { e }` | `let f = fn(x) { e }` | `Let("f", Lam(("x", Hole(-1)), e), body)` |
| `let x = e` | (same) | `Let("x", e, body)` |
| `a + b` | `+(a, b)` | `App(Var("+"), App(App(Var("+"), a), b))` |
| `-x` | `negate(x)` | `App(Var("-"), x)` |
| `if c { a } else { b }` | `match c { | True -> a | False -> b }` | `Match(c, [Case(True, a), Case(False, b)])` |
| `for x in c { e }` | `foldl(\(acc, x) -> e, (), c)` | `App(Lam((acc, x), e), Unit(), c)` |
| `while c { e }` | `fix loop -> if c { e; loop }` | `Fix("loop", If(c, e, Call("loop", [])))` |
| `loop { e }` | `fix loop -> e; loop` | `Fix("loop", App(e, Call("loop", [])))` |
| `break` | `call_break(loop, value)` | `Call("break", [loop, value])` |
| `continue` | `call_continue(loop, value)` | `Call("continue", [loop, value])` |
| `yield expr` | `Stream.cons(expr, tail)` | `Call("Stream.cons", [expr, tail])` |
| `mut x = e` | `let x_N = e` (unique name) | `Let("x_N", e, body)` |
| `{ e1; e2; e3 }` | `do { e1; e2; e3 }` | `DoBlock([e1, e2, e3], e3)` |
| `x |> f` | `f(x)` | `App(f, x)` |
| `let x <- e` | `match e { | Some(x) -> ... }` | `Match(e, [Case(Some(x), body)])` |
| `comptime { e }` | (evaluated at compile time) | `Comptime(e)` |
| `run e` | (evaluated and printed) | `Call("run", [e])` |
| `test "name" { e }` | (evaluated as test) | `Call("test", ["name", e])` |

**Note on operators:** Operators (`+`, `-`, etc.) desugar to function calls with operator names. The function `"+"` handles overloading via pattern matching on argument types (see 10-operator-overloading.md). Single-definition functions and overloaded functions both use the same pattern-matching mechanism.
