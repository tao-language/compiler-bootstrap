# Tao High-Level Language Specification

## Design Philosophy

Tao is a **high-level language** that desugars to Core. It provides:
- Syntactic sugar for Core constructs
- High-level features (for-loops, while-loops, mutable variables, etc.)
- Module system with imports
- Type declarations with constructors
- FFI integration
- Test framework

Everything in Tao is **desugared to Core** before type checking. Tao is never type-checked directly — it's always translated to Core first.

## Directory Structure

```
src/tao/
├── ast.gleam              # Tao AST (Stmt, Expr, Pattern, TypeAst)
├── lexer.gleam            # Tao tokenizer
├── syntax.gleam           # Tao parser + formatter (uses grammar lib)
├── desugar.gleam          # Expr → Term desugaring
├── language_config.gleam  # Language configuration
├── global_context.gleam   # Module context management
├── import_resolver.gleam  # Import resolution
├── import_ast.gleam       # Import AST helpers
├── compiler.gleam         # Multi-file compilation pipeline
├── ffi.gleam              # FFI builtin definitions
├── error_reporter.gleam   # Tao-specific error reporting
├── test_api.gleam         # Test framework
├── test_parser.gleam      # Test annotation parsing
├── test_reporter.gleam    # Test output formatting
└── test_filter.gleam      # Test name matching
```

## Type Definitions

### Expressions

```gleam
/// High-level expressions (string-based variable names)
pub type Expr {
  /// Variable: x
  Var(name: String, span: Span)
  
  /// Literal: 42, 3.14, "hello"
  Lit(Literal, span: Span)
  
  /// Lambda: fn(x: a) -> a
  Lambda(List(Param), Expr, span: Span)
  
  /// Application: f(x)
  Call(Expr, List(Expr), span: Span)
  
  /// Binary operator: a + b
  BinOp(Expr, BinOp, Expr, span: Span)
  
  /// Unary operator: -x, !x
  UnaryOp(UnaryOp, Expr, span: Span)
  
  /// Record construction: { x: 1, y: 2 }
  Record(List(RecordField), span: Span)
  
  /// Field access: record.field
  FieldAccess(Expr, String, span: Span)
  
  /// Constructor: Some(x), None, True, False
  Ctr(String, List(Expr), span: Span)
  
  /// Pattern match: match x { | Some(y) -> y | None -> 0 }
  Match(Expr, List(MatchClause), span: Span)
  
  /// If expression: if cond { a } else { b }
  If(Expr, Expr, Option(Expr), span: Span)
  
  /// Type annotation: (e : T)
  Annotated(Expr, TypeAst, span: Span)
  
  /// Hole: _
  Hole(span: Span)
  
  /// Comptime: comptime expr
  Comptime(Expr, span: Span)

  /// Block expression (mutable vars, loops, etc.)
  Block(List(Stmt), span: Span)
}

/// Binary operators (desugared to Core function calls)
pub type BinOp {
  OpAdd OpSub OpMul OpDiv OpMod
  OpEq OpNeq OpLt OpGt OpLte OpGte
  OpAnd OpOr OpPipe OpConcat
}

/// Unary operators (desugared to Core function calls)
pub type UnaryOp {
  OpNegate OpNot
}

/// Record field: x: value
pub type RecordField {
  RecordField(name: String, value: Expr)
}

/// Match clause: pattern -> body [if guard]
pub type MatchClause {
  MatchClause(
    pattern: Pattern,
    guard: Option(Expr),
    body: Expr,
    span: Span,
  )
}

/// Function parameter: param: Type
pub type Param {
  Param(name: String, type_: Option(TypeAst), span: Span)
}
```

### Statements

```gleam
/// Module-level statements
pub type Stmt {
  /// let [mut] x [: Type] = expr
  Let(String, Bool, Option(TypeAst), Expr, span: Span)
  
  /// fn name(params) [: Type] { body }
  Fn(String, List(String), List(Param), Option(TypeAst), Expr, span: Span)
  
  /// import path [as alias] { names }
  Import(ImportItem, span: Span)
  
  /// type Name = Ctor | Ctor(args) | ...
  TypeDef(String, List(String), List(Constructor), span: Span)
  
  /// Expression statement: expr
  ExprStmt(Expr, span: Span)
}
```

### Type AST (for annotations)

```gleam
/// Type annotations in Tao source
pub type TypeAst {
  /// Type variable: a, b, T
  TVar(String, span: Span)
  
  /// Type application: Maybe(a), List(Int)
  TApp(String, List(TypeAst), span: Span)
  
  /// Function type: (Int, Int) -> Int
  TFn(List(TypeAst), TypeAst, span: Span)
  
  /// Record type: { x: Int, y: Int = 0 }
  TRecord(List(#(String, TypeAst, Option(Expr))), span: Span)
  
  /// Tuple type: (Int, String)
  TTuple(List(TypeAst), span: Span)
  
  /// Hole: _
  THole(span: Span)
}
```

### Pattern

```gleam
/// Patterns in match expressions and let bindings
pub type Pattern {
  PAny(span: Span)               // Wildcard: _
  PVar(String, span: Span)       // Variable: x
  PLit(Literal, span: Span)      // Literal: 42
  PCtr(String, List(Pattern), span: Span)  // Constructor: Some(x)
  PRecord(List(String), span: Span)         // Record: { x, y }
  PTuple(List(Pattern), span: Span)         // Tuple: (a, b)
  PList(List(Pattern), Option(String), span: Span)  // List: [h, ..t]
  POr(List(Pattern), span: Span)             // Or: a | b
  PAs(Pattern, String, span: Span)           // As: x @ Some(_)
}
```

### Import System

```gleam
/// Import item (selective or wildcard)
pub type ImportItem {
  ImportAll(String)              // import path *
  ImportSelective(String, Option(String), List(ImportName))  // import path as alias { name1, name2 as n2 }
}

pub type ImportName {
  ImportName(String, Option(String))  // (name, optional_alias)
}
```

### Constructor

```gleam
/// Type constructor definition
pub type Constructor {
  Constructor(
    name: String,
    fields: List(#(String, TypeAst, Option(Expr))), // name, type, default valu
    span: Span,
  )
}
```

## Desugaring: Tao → Core

### High-Level Features → Core Terms

All Tao high-level features are desugared to Core terms:

| Tao Feature | Desugars To | Core Term |
|-------------|-------------|-----------|
| `fn f(x) { e }` | `let f = fn(x) => e` | `Let("f", Lam(("x", e)), body)` |
| `let x = e` | (same) | `Let("x", e, body)` |
| `a + b` | `add(a, b)` | `Call("add", [a, b])` |
| `-x` | `negate(x)` | `Call("negate", [x])` |
| `if cond { a } else { b }` | `match cond { | True -> a | False -> b }` | `Match(cond, [Case(True, a), Case(False, b)])` |
| `for x in collection { e }` | `foldl(\(acc, x) -> e, init, collection)` | `App(Lam((acc, x), e), init, collection)` |
| `while cond { e }` | `fix loop -> if cond { e; loop }` | `Fix("loop", If(cond, e, Call("loop", [])))` |
| `loop { e }` | `fix loop -> e; loop` | `Fix("loop", App(e, Call("loop", [])))` |
| `break` | `match result { | Some(v) -> v | None -> ... }` | Desugars to `Maybe` pattern match |
| `continue` | `break with loop continuation` | Desugars to `Maybe` with fixpoint |
| `return expr` | `match result { | Some(v) -> v | None -> ... }` | Desugars to `Maybe` pattern match |
| `yield expr` | `Stream.yield(expr)` | `Call("Stream.yield", [expr])` |
| `mut x = e` | `let x = e` (immutable) | `Let("x", e, body)` (Tao immutability) |
| `{ e1; e2; e3 }` | `do { e1; e2; e3 }` | `DoBlock([e1, e2, e3], e3)` |
| `test "name" { e }` | (runtime test) | `Run(comptime e)` |

### For-Loop Desugaring (Detailed)

```tao
// Tao source
for x in [1, 2, 3] {
  print(x)
}
```

```gleam
// Desugars to Core (simplified)
let iter = iterator([1, 2, 3])
let loop = fix \acc ->
  match next(iter) {
    | Some(x) -> (print(x); loop acc)
    | None -> acc
  }
loop ()
```

### While-Loop Desugaring (Detailed)

```tao
// Tao source
while x > 0 {
  x = x - 1
}
```

```gleam
// Desugars to Core
let loop = fix \_ ->
  match (>)(x, 0) {
    | True -> (x = x - 1; loop ())
    | False -> ()
  }
loop ()
```

### Mutable Variable Desugaring

Tao's mutable variables are desugared to immutable Core. The mutability is enforced at the Tao level through a separate tracking mechanism (a mutable variable counter in the desugarer context). Core itself remains purely functional.

```tao
// Tao source
mut counter = 0
counter = counter + 1
```

```gleam
// Desugars to separate let bindings
let counter_0 = 0
let counter_1 = counter_0 + 1
let counter_2 = counter_1 + 1
```

Each "mutation" creates a new binding. The desugarer tracks variable names and generates unique names.

### Generator / Yield Desugaring

```tao
// Tao source
let nums = {
  for x in [1, 2, 3] {
    yield x * 2
  }
}
```

```gleam
// Desugars to Core
let nums = Stream.from_list([1, 2, 3])
  |> Stream.map(\x -> x * 2)
  |> Stream.to_list
```

The `Stream` type is defined in the Tao stdlib, not in Core:
```tao
type Stream(a) = Cons(head: a, tail: Stream(a)) | Empty
```

### Operator Overloading

```gleam
/// Operator resolution in Tao
pub type OverloadMode {
  LiteralOverload    // 42 can be Int or Float (ILitT / FLitT)
  FunctionOverload   // Same function name with different types (handled by Tao FFI)
}
```

**Literal overloading:** During type checking in Core, `ILitT` unifies with any concrete integer type (I32T, I64T, etc.), and `FLitT` unifies with any float type. This provides automatic literal overloading.

**Function overloading:** Tao supports FFI-based function overloading. The same name can have multiple FFI entries with different argument types. The type checker tries each in order:

```gleam
// In ffi.gleam — Tao can define multiple entries for the same name
let ffi_entries = [
  #("add", int_add, [I32T, I32T], I32T),    // add(Int, Int) -> Int
  #("add", float_add, [F64T, F64T], F64T),  // add(Float, Float) -> Float
]

// During type checking, unify arguments against each entry in order
```

## Language Configuration

```gleam
/// Language-specific configuration (Tao only, not in Core)
pub type LanguageConfig {
  LanguageConfig(
    truth_constructor: String,   // "True" for Tao
    false_constructor: String,   // "False" for Tao
    constructors: List(#(String, Constructor)),  // Available constructors
    operators: List(#(String, Operator)),  // Available operators
    primitives: List(#(String, Primitive)),  // Primitive types (Int, Float, etc.)
  )
}
```

**Design rationale:** Tao's configuration is separate from Core. Core receives the resolved constructor environment (`CtrEnv`) and FFI entries (`List(FfiEntry)`) from Tao's desugarer. Core knows nothing about which language is using it.

## Example: Tao Programs

### Fibonacci (Iterative with Mutable Variables)

```tao
// Tao source
fn fib(n: Int) -> Int {
  mut a = 0
  mut b = 1
  mut i = 0
  while i < n {
    let temp = a
    a = b
    b = temp + b
    i = i + 1
  }
  a
}
```

```gleam
// Desugars to Core (pseudocode)
let fib = fn(n) ->
  let a_0 = 0
  let b_0 = 1
  let i_0 = 0
  let loop = fix \_ ->
    if <(i, n) {
      let a_1 = b_0
      let b_1 = +(a_0, b_0)
      let i_1 = +(i_0, 1)
      loop ()
    } else {
      a_0
    }
  loop ()
```

### Fold and Map (Higher-Order Functions)

```tao
// Tao source
fn map(f, xs) {
  match xs {
    | [] -> []
    | [h, ..t] -> [f(h), ..map(f, t)]
  }
}

fn filter(p, xs) {
  match xs {
    | [] -> []
    | [h, ..t] ->
      if p(h) {
        [h, ..filter(p, t)]
      } else {
        filter(p, t)
      }
  }
}

// Usage
let nums = [1, 2, 3, 4, 5]
let doubled = map(\x -> x * 2, nums)
let evens = filter(\x -> x == 0, doubled)
```

### Generator (Stream)

```tao
// Tao source
fn range(start, end) {
  if start >= end {
    Stream.empty()
  } else {
    let tail = range(start + 1, end)
    Stream.cons(start, tail)
  }
}

let nums = range(1, 10)
let doubled = map(\x -> x * 2, nums)
let sum = foldl(\(acc, x) -> acc + x, 0, doubled)
```

## Module System

### Import Resolution

```gleam
/// Import resolution in Tao
pub type ImportResolution {
  Success(
    module: Module,
    public_names: List(String),
    public_values: List(#(String, Value)),
  )
  Error(ImportError)
}

pub type ImportError {
  ModuleNotFound(path: String)
  CircularImport(from: String, to: String)
  ImportError(message: String, span: Span)
}
```

### Import Desugaring

```tao
// Tao source
import math { sin, cos as cosine }
import std/io *

// Desugars to Core
let math = @math  // Module reference
let sin = math.sin
let cosine = math.cos
let io = @std.io
```

All imports become `let` bindings in the desugared Core term. The module system is purely a compile-time feature — at runtime, modules don't exist.

## Testing Strategy

### Unit Tests (desugar_test.gleam)

```gleam
should("desugar function to let binding with lambda") {
  desugar(StmtFn("add", [], [Param("x", None)], None, BinOp(Lit(1), OpAdd, Lit(2)))) ==
    TermLet("add", TermLam(("x", TermLit(Int(3)))), TermUnit)
}

should("desugar for-loop to fold") {
  desugar(StmtFor("x", LitList([1, 2, 3]), [StmtExpr(Call("print", [Var("x")])])) ==
    TermLet("iter", TermCall("iterator", [LitList([1, 2, 3])]),
    TermLet("loop", TermFix("loop", TermIf(
      TermCall("next", [Var("iter")]),
      TermMatch(Var("iter"), [Case(PCtr("Some", PVar("x")), TermApp(Var("loop"), TermUnit))],
      TermApp(Var("loop"), TermUnit))
```

### Integration Tests (compiler_test.gleam)

```gleam
should("compile a complete Tao program") {
  let source = read_file("examples/tao/programs/fib.tao")
  let result = compile(source)
  result.errors == []
  result.value == VLit(I32(55))  // fib(10)
}
```

### Golden Tests (golden_test.gleam)

```gleam
should("round-trip Tao through compile") {
  let source = read_file("example.tao")
  let result = compile(source)
  let output = format(result.term)
  write_file("example.tao.output", output)
}
```
