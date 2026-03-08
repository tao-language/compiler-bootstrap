# Core Language Syntax Specification

> **Status**: Implemented - Core functionality complete
> **Purpose**: Minimal, explicit, fast-to-parse syntax for the core language
> **Use Case**: Code serialization, cluster distribution, debugging

---

## Design Philosophy

The core language is **"JSON with types, functions, and pattern matching"**:

1. **Explicit** - No inference, everything visible
2. **Unambiguous** - One way to write everything
3. **Fast to parse** - Clear delimiters, no precedence
4. **Compact** - Minimal syntax overhead
5. **Self-contained** - Can be sent across network and evaluated
6. **Readable** - Humans can debug when needed
7. **Functional** - No objects, no mutation, no inheritance
8. **Error Resilient** - Preserve structure on errors for better IDE support

---

## Why Not Object-Oriented?

**Neither the core language nor the high-level language support object-oriented features.**

### Problems with OO

| Issue | Why It Matters |
|-------|---------------|
| **Hidden complexity** | Method dispatch, virtual tables, dynamic binding |
| **Inheritance** | Fragile base class problem, diamond inheritance |
| **Mutable state** | Race conditions, hard to reason about |
| **Encapsulation** | Hides complexity instead of eliminating it |
| **`this` binding** | Confusing, context-dependent |
| **Side effects** | Hard to parallelize, distribute, or GPU-accelerate |

### Why Functional?

| Benefit | Why It Matters |
|---------|---------------|
| **Immutability** | Safe to share across threads/machines |
| **Pure functions** | Easy to parallelize and cache |
| **Explicit data flow** | Clear what depends on what |
| **Pattern matching** | Exhaustive, compiler-verified |
| **Type safety** | Catch errors at compile time |
| **Composability** | Functions compose naturally |
| **Distribution** | No hidden state, easy to serialize |
| **GPU-friendly** | No mutation, easy to vectorize |

### Design Principle

> **Data + Functions ≠ Objects**
>
> - **Data** is just data (records, no methods)
> - **Functions** are just functions (no `this`, no classes)
> - **Composition** over inheritance
> - **Immutability** by default

---

## Syntax Decisions

### Arrow Style: `->` vs `=>`

**Decision: Use `->`**

| Aspect | `->` | `=>` |
|--------|------|------|
| **Precedent** | Haskell, OCaml, Rust | TypeScript, JavaScript |
| **Meaning** | "maps to" / "produces" | "implies" / "arrow" |
| **Consistency** | Same as match branches | Different from match |
| **Visual weight** | Lighter | Heavier |
| **Functional heritage** | Strong | Weaker |

**Why `->` is better for core language:**

1. **Consistent with pattern matching** - Same arrow everywhere
2. **Functional heritage** - Core language is functional, not OO
3. **Lighter syntax** - Less visual noise
4. **Clearer semantics** - "maps to" is more precise than "arrow"

```
-- With -> (CHOSEN)
(x: Int) -> Int
match x {
| A(a) -> a
| B -> 0
}

-- With => (rejected)
(x: Int) => Int
match x {
| A(a): => a
| B: => 0
}
```

### Match Syntax: OCaml-Style

```
-- OCaml-style (CHOSEN)
match x {
| A -> e
| B -> e
}

-- TS-style (rejected)
match(x) {
  case A: => e
  case B: => e
}
```

**Benefits:**
- No parentheses needed (no ambiguity)
- No `case` keyword (less noise)
- `|` clearly separates patterns
- Same `->` as functions (consistent)

### Pattern Guards

```
-- With guards
match n {
| x if x > 0 -> "positive"
| x if x < 0 -> "negative"
| _ -> "zero"
}

-- Core AST
Match(
  Var("n"),
  Var("String"),
  [
    Case(PVar("x"), Some(App(App(Var(">"), Var("x")), Lit(0))), Lit("positive")),
    Case(PVar("x"), Some(App(App(Var("<"), Var("x")), Lit(0))), Lit("negative")),
    Case(PAny, None, Lit("zero"))
  ]
)
```

**Implementation:**
- `Case` has optional `guard: Option(Term)` field
- Guard must have type `Bool`
- Evaluated after pattern match, before body
- Guarded cases are "partial" for exhaustiveness checking

### Primitive Operations

```
-- Arithmetic primitives
+(1, 2)           -- PrimOp(Add, [1, 2])
-(5, 3)           -- PrimOp(Subtract, [5, 3])
*(2, 3)           -- PrimOp(Multiply, [2, 3])
/(10, 2)          -- PrimOp(Divide, [10, 2])
%(10, 3)          -- PrimOp(Modulo, [10, 3])

-- Comparison primitives
>(5, 3)           -- PrimOp(GreaterThan, [5, 3])
<(3, 5)           -- PrimOp(LessThan, [3, 5])
>=(5, 5)          -- PrimOp(GreaterThanOrEqual, [5, 5])
<=(5, 5)          -- PrimOp(LessThanOrEqual, [5, 5])
==(1, 1)          -- PrimOp(Equals, [1, 1])
!=(1, 2)          -- PrimOp(NotEquals, [1, 2])

-- Logical primitives
&&(true, false)   -- PrimOp(And, [true, false])
||(true, false)   -- PrimOp(Or, [true, false])
!(false)          -- PrimOp(Not, [false])

-- Core AST
PrimOp(Add, [Lit(1), Lit(2)])
PrimOp(GreaterThan, [Var("x"), Lit(0)])
```

**Why Primitives?**
- **Efficiency** - Direct CPU instructions, no function call overhead
- **Type safety** - Primitive ops have fixed, known types
- **Optimization** - Compiler can optimize primitives aggressively
- **Serialization** - Compact encoding for network transfer

### Effect System: Algebraic Effects

```
-- Effect types
IO<Int>           -- Effectful computation returning Int
State<Counter, Int>  -- Stateful computation with Counter state
Error<String, Int>   -- Computation that can fail with String error

-- Effect operations
perform ReadLine(): String    -- Perform IO effect
perform Write(s): Unit        -- Perform IO effect
perform Get(): State          -- Get current state
perform Put(s): Unit          -- Set state
perform Raise(e): Error       -- Raise error

-- Handling effects
handle computation {
  return x -> x,
  ReadLine() -> k(getLine()),
  Write(s) -> k(print(s)),
  Get() -> k(currentState),
  Put(s) -> k(unit, s),
  Raise(e) -> handleError(e)
}

-- Core AST
Perform(effect, args, continuation)
Handle(computation, handlers)
```

**Why Algebraic Effects?**
- **Composability** - Effects compose naturally
- **Testability** - Easy to mock effects
- **Separation** - Effect logic separate from business logic
- **Distribution** - Effects can be handled remotely

### Terminology: No Objects

| Avoid | Use Instead |
|-------|-------------|
| `obj`, `object` | `record`, `data` |
| `class` | `type`, `record` |
| `instance` | `value`, `term` |
| `method` | `function` |
| `inheritance` | N/A (not supported) |
| `polymorphism` | `generics`, `parametric types` |

**Rationale:** Core language is **functional**, not object-oriented. Records are just data structures with named fields.

---

## Complete Syntax

### 1. **Universe Types**

```
Type<0>      -- Type₀
Type<1>      -- Type₁
Type<k>      -- Typeₖ
```

### 2. **Literals**

```
-- Numbers
42
-17
3.14
-2.5

-- Booleans
true
false

-- Strings
"hello"

-- Literal types
I32
I64
F32
F64
```

### 3. **Variables**

```
x
myVariable
_underscore
```

### 4. **Lambda Abstraction**

```
-- Simple lambda
(x) -> x + 1

-- With type annotation
(x: Int) -> x + 1

-- Multiple arguments (curried - each arg is its own lambda)
(x: Int, y: Int) -> x + y

-- Named lambda (top-level)
add(x: Int, y: Int): Int -> x + y

-- Core term:
Lam("add", Lam("x", Lam("y", App(App(Var("add"), Var("x")), Var("y")))))
```

### 5. **Function Application**

```
-- Application (parentheses, comma-separated)
f(x)
f(x, y)
add(1, 2)

-- Nested application
f(g(x))

-- Core term:
App(App(Var("add"), Lit(1)), Lit(2))
```

### 6. **Primitive Operations**

```
-- Arithmetic
+(1, 2)
-(5, 3)
*(2, 3)
/(10, 2)
%(10, 3)

-- Comparison
>(5, 3)
<(3, 5)
>=(5, 5)
<=(5, 5)
==(1, 1)
!=(1, 2)

-- Logical
&&(true, false)
||(true, false)
!(false)

-- Core term:
PrimOp(Add, [Lit(1), Lit(2)])
PrimOp(GreaterThan, [Var("x"), Lit(0)])
```

### 7. **Effect Operations**

```
-- IO effects
perform ReadLine(): String
perform Write("hello"): Unit

-- State effects
perform Get(): Counter
perform Put(newCounter): Unit

-- Error effects
perform Raise("error"): Never

-- Core term:
Perform("ReadLine", [], Lam("result", ...))
Perform("Write", [Lit("hello")], Lam("result", ...))
```

### 8. **Effect Handling**

```
-- Handle IO effects
handle computation {
| return(x) -> x
| ReadLine() -> k(getLine())
| Write(s) -> k(print(s))
}

-- Handle state effects
handle computation with state {
| return(x) -> (x, finalState)
| Get() -> k(currentState, currentState)
| Put(s) -> k(unit, s)
}

-- Core term:
Handle(
  computation,
  [
    Handler("return", Lam("x", Var("x"))),
    Handler("ReadLine", Lam("_", Lam("k", App(Var("k"), App(Var("getLine"), Unit))))),
    Handler("Write", Lam("s", Lam("k", App(Var("k"), App(Var("print"), Var("s"))))))
  ]
)
```

### 9. **Dependent Function Types (Pi Types)**

```
-- Simple function type
Int -> Int

-- Named argument (for dependent types)
(x: Int) -> Int

-- Dependent: output type mentions input
(n: Nat) -> Vec<Int, n>

-- Core term:
Pi("n", Var("Nat"), App(Vec, Int, Var("n")))
```

### 10. **Type Annotations**

```
-- Annotated term
(x: Int)
(42: Int)

-- Annotated lambda
(x: Int): Int -> x

-- Function return type
add(x: Int, y: Int): Int -> x + y

-- Core term:
Ann(Var("x"), Var("Int"))
```

### 11. **Records**

```
-- Record construction
{ x: 1, y: 2 }
Point { x: 1, y: 2 }

-- Field access
record.x
record.y

-- Record update
{ ...record, x: 3 }

-- Core term:
Rcd([("x", Lit(42)), ("y", Lit(2))])
Dot(Var("record"), "x")
```

### 12. **Type Definitions (NOT Classes)**

```
-- Type declaration (NOT a class!)
type Option<A> {
| Some(A)
| None()
}

-- With explicit types
type List<A> {
| Nil(): List<A>
| Cons(head: A, tail: List<A>): List<A>
}

-- GADT style
type Vec<A, n: Nat> {
| VNil(): Vec<A, Zero>
| VCons(head: A, n: Nat, tail: Vec<A, n>): Vec<A, Succ(n)>
}

-- Record type (just data, no methods!)
type Point {
  x: Int
  y: Int
}

-- Core term (constructor definitions):
CtrDef([], Var("A"), App(App(Vec, Var("A")), Zero))
CtrDef(["n"], Var("A"), App(App(Vec, Var("A")), App(Succ, Var("n"))))
```

### 13. **Constructors (NOT Methods)**

```
-- Constructor application (NOT method calls!)
Some(42)
None()
Cons(1, Cons(2, Nil()))
Ok(value)
Err("error message")

-- With explicit type
Some<Int>(42)

-- Core term:
Ctr("Some", Lit(42))
Ctr("None", Unit)
```

### 14. **Pattern Matching with Guards**

```
-- Basic match (no parentheses, no 'case')
match opt {
| Some(x) -> x
| None -> 0
}

-- With motive (explicit return type)
match opt: Int {
| Some(x) -> x
| None -> 0
}

-- With guards
match n {
| x if x > 0 -> "positive"
| x if x < 0 -> "negative"
| _ -> "zero"
}

-- Multiple patterns
match n {
| Zero -> "zero"
| Succ(Zero) -> "one"
| Succ(Succ(_)) -> "many"
}

-- Record patterns
match record {
| { x: 0, y: 0 } -> "origin"
| { x, y } -> `point at (${x}, ${y})`
}

-- As patterns
match list {
| x @ Cons(h, t) -> h
| Nil -> 0
}

-- Core term with guard:
Match(
  Var("n"),
  Var("String"),
  [
    Case(PVar("x"), Some(App(App(Var(">"), Var("x")), Lit(0))), Lit("positive")),
    Case(PVar("x"), Some(App(App(Var("<"), Var("x")), Lit(0))), Lit("negative")),
    Case(PAny, None, Lit("zero"))
  ]
)
```

### 15. **Let Bindings**

```
-- Let expression (semicolon separates)
let x = 42;
x + 1

-- With type
let x: Int = 42;
x + 1

-- Multiple lets (sequential)
let x = 1;
let y = 2;
x + y

-- Recursive let (for mutually recursive functions)
let rec length = (list): Int -> match list {
  | Nil -> 0
  | Cons(_, tail) -> 1 + length(tail)
};
length(myList)

-- Core term:
App(
  Lam("x", Lam("y", App(App(Var("+"), Var("x")), Var("y")))),
  Lit(1)
)(Lit(2))
```

### 16. **Holes (Metavariables)**

```
-- Hole (for type inference / holes in code)
?
?0
?1

-- With expected type
?<Int>
?_

-- Core term:
Hole(0)
Hole(1)
```

### 17. **Function Definitions (NOT Methods)**

```
-- Top-level function (NOT a method!)
add(x: Int, y: Int): Int -> x + y

-- Generic function
id<A>(x: A): A -> x

-- With pattern matching
length(list): Int -> match list {
| Nil -> 0
| Cons(_, tail) -> 1 + length(tail)
}

-- Functions operate on data (NOT methods on objects)
map(f: (A) -> B, list: List<A>): List<B> -> match list {
| Nil -> Nil
| Cons(head, tail) -> Cons(f(head), map(f, tail))
}

-- Effectful function
readAndPrint(): IO<Unit> -> {
  let line = perform ReadLine();
  perform Write(line)
}
```

---

## Complete Examples

### Example 1: Identity Function

```
-- Surface syntax
id<A>(x: A): A -> x

-- Core term
Lam("id", Lam("x", Ann(Var("x"), Var("A"))))

-- With explicit Pi type
Lam("id", Lam("x", Ann(Var("x"), Pi("_", Var("Type"), Var("A")))))
```

### Example 2: Arithmetic with Primitives

```
-- Surface
add(x: Int, y: Int): Int -> +(x, y)

-- Core term
Lam("add", Lam("x", Lam("y", PrimOp(Add, [Var("x"), Var("y")]))))

-- Comparison with guard
isPositive(x: Int): Bool -> match x {
| _ if >(x, 0) -> true
| _ -> false
}

-- Core term
Lam("isPositive",
  Lam("x",
    Match(Var("x"), Var("Bool"), [
      Case(PAny, Some(PrimOp(GreaterThan, [Var("x"), Lit(0)])), Lit(true)),
      Case(PAny, None, Lit(false))
    ])
  )
)
```

### Example 3: Effectful IO

```
-- Surface
readAndPrint(): IO<Unit> -> {
  let line = perform ReadLine();
  perform Write(line)
}

-- Core term
Lam("readAndPrint",
  Perform("ReadLine", [],
    Lam("line",
      Perform("Write", [Var("line")],
        Lam("_", Unit)
      )
    )
  )
)
```

### Example 4: State Handling

```
-- Surface
counter(): State<Int, Int> -> {
  let current = perform Get();
  perform Put(+(current, 1));
  current
}

-- Core term
Lam("counter",
  Perform("Get", [],
    Lam("current",
      Perform("Put", [PrimOp(Add, [Var("current"), Lit(1)])],
        Lam("_", Var("current"))
      )
    )
  )
)

-- Handling state
handle counter() with state 0 {
| return(x) -> (x, finalState)
| Get() -> k(currentState, currentState)
| Put(s) -> k(unit, s)
}
```

### Example 5: Option Map (Functional, NOT OO)

```
-- Surface (function takes data, NOT method on object)
map<A, B>(f: (A) -> B, opt: Option<A>): Option<B> -> match opt {
| Some(x) -> Some(f(x))
| None -> None()
}

-- Core term
Lam("map",
  Lam("f",
    Lam("opt",
      Match(
        Var("opt"),
        App(Option, Var("B")),
        [
          Case(PCtr("Some", PVar("x")), Ctr("Some", App(Var("f"), Var("x")))),
          Case(PCtr("None", PAny), Ctr("None", Unit))
        ]
      )
    )
  )
)
```

### Example 6: Vector Head (Dependent Type)

```
-- Surface
vhead<A, n: Nat>(v: Vec<A, Succ(n)>): A -> match v {
| VCons(x, _, _) -> x
}

-- Core term
Lam("vhead",
  Lam("v",
    Match(
      Var("v"),
      Var("A"),
      [
        Case(PCtr("VCons", PAs(PVar("x"), "_")), Var("x"))
      ]
    )
  )
)
```

### Example 7: Natural Numbers with Guards and Primitives

```
-- Type definition (NOT a class!)
type Nat {
| Zero()
| Succ(n: Nat)
}

-- Sign function with guards and primitives
sign(n: Nat): Int -> match n {
| Zero -> 0
| Succ(m) if >(m, 10) -> 1
| Succ(_) -> -(0, 1)
}

-- Core term for sign
Lam("sign",
  Lam("n",
    Match(
      Var("n"),
      Var("Int"),
      [
        Case(PCtr("Zero", PAny), None, Lit(0)),
        Case(PCtr("Succ", PVar("m")), 
          Some(PrimOp(GreaterThan, [Var("m"), Lit(10)])),
          Lit(1)),
        Case(PCtr("Succ", PAny), None, PrimOp(Subtract, [Lit(0), Lit(1)]))
      ]
    )
  )
)
```

---

## Wire Format (JSON-like Serialization)

For network transmission, core terms serialize to JSON:

```
-- Core term
PrimOp(Add, [Lit(1), Lit(2)])

-- JSON serialization
{
  "tag": "PrimOp",
  "op": "Add",
  "args": [
    { "tag": "Lit", "value": 1 },
    { "tag": "Lit", "value": 2 }
  ]
}

-- Effect handling
Perform("ReadLine", [], Lam("result", ...))

-- JSON
{
  "tag": "Perform",
  "effect": "ReadLine",
  "args": [],
  "continuation": { "tag": "Lam", "name": "result", ... }
}

-- Binary serialization (more compact)
[PRIMOP, ADD, [LIT, 1], [LIT, 2]]
[PERFORM, "ReadLine", [], [LAM, "result", ...]]
```

### Serialization Format

```
-- Term variants
type Term =
  | { tag: "Typ", universe: number }
  | { tag: "Lit", value: Literal }
  | { tag: "LitT", typ: LiteralType }
  | { tag: "Var", index: number }  -- De Bruijn index
  | { tag: "Hole", id: number }
  | { tag: "Rcd", fields: [string, Term][] }
  | { tag: "Ctr", tag: string, arg: Term }
  | { tag: "Dot", arg: Term, field: string }
  | { tag: "Ann", term: Term, typ: Term }
  | { tag: "Lam", name: string, body: Term }
  | { tag: "Pi", name: string, in: Term, out: Term }
  | { tag: "App", fun: Term, arg: Term }
  | { tag: "Match", arg: Term, motive: Term, cases: Case[] }
  | { tag: "PrimOp", op: PrimOpType, args: Term[] }  -- NEW
  | { tag: "Perform", effect: string, args: Term[], continuation: Term }  -- NEW
  | { tag: "Handle", computation: Term, handlers: Handler[] }  -- NEW

-- Primitive operation types
type PrimOpType =
  | "Add" | "Subtract" | "Multiply" | "Divide" | "Modulo"
  | "GreaterThan" | "LessThan" | "GreaterThanOrEqual" | "LessThanOrEqual"
  | "Equals" | "NotEquals"
  | "And" | "Or" | "Not"

-- Case with guard
type Case = {
  pattern: Pattern,
  guard: Option<Term>,  -- Optional guard
  body: Term,
  span: Span
}

-- Handler for effects
type Handler = {
  name: string,
  params: string[],
  body: Term
}

-- Compact binary encoding
const TAGS = {
  Typ: 0, Lit: 1, LitT: 2, Var: 3, Hole: 4,
  Rcd: 5, Ctr: 6, Dot: 7, Ann: 8,
  Lam: 9, Pi: 10, App: 11, Match: 12,
  PrimOp: 13, Perform: 14, Handle: 15
}

const PRIMOPS = {
  Add: 0, Subtract: 1, Multiply: 2, Divide: 3, Modulo: 4,
  GreaterThan: 5, LessThan: 6, GreaterThanOrEqual: 7, LessThanOrEqual: 8,
  Equals: 9, NotEquals: 10,
  And: 11, Or: 12, Not: 13
}
```

---

## Grammar (EBNF)

```ebnf
-- Core language grammar (OCaml/TS hybrid, functional)

term ::= literal
       | var
       | hole
       | '(' var (':' type)? ')' '->' term    -- Lambda
       | term '(' args? ')'                   -- Application
       | prim_op '(' args ')'                 -- Primitive operation
       | 'perform' effect '(' args? ')'       -- Effect operation
       | 'handle' term 'with' handlers        -- Effect handling
       | term ':' type                        -- Annotation
       | 'match' var (':' term)? '{' cases '}'
       | 'let' ('rec' var)? (':' term)? '=' term ';' term
       | '{' fields? '}'                      -- Record
       | '{' '...' term ',' fields '}'        -- Record update
       | term '.' var                         -- Field access
       | constr '(' args? ')'                 -- Constructor
       | '(' term ')'

args ::= term (',' term)*

literal ::= Int | Float | Bool | String
          | 'I32' | 'I64' | 'F32' | 'F64'
          | 'Type' '<' Int '>'

var ::= IDENT
hole ::= '?' Int?

type ::= term                            -- Types are terms
       | type '->' type                  -- Function type

prim_op ::= '+' | '-' | '*' | '/' | '%'
          | '>' | '<' | '>=' | '<=' | '==' | '!='
          | '&&' | '||' | '!'

effect ::= IDENT

handlers ::= '{' ('|' handler)+ '}'
handler ::= 'return' '(' var ')' '->' term
          | effect_name '(' params? ')' '->' term

cases ::= ('|' pattern ('if' term)? '->' term)+

pattern ::= '_'
          | var
          | literal
          | constr '(' patterns? ')'
          | '{' field_patterns? '}'
          | var '@' pattern              -- As pattern

patterns ::= pattern (',' pattern)*

field_patterns ::= var (':' pattern)? (',' var (':' pattern)?)*

fields ::= (var ':' term) (',' (var ':' term))*

constr ::= UPPERCASE_IDENT

fn_def ::= var type_params? '(' params? ')' (':' type)? '->' term
params ::= param (',' param)*
param ::= var ':' type

type_params ::= '<' var (':' type)? (',' var (':' type)?)* '>'

type_def ::= 'type' var type_params? '{' ('|' constr_def)* '}'
constr_def ::= constr '(' params? ')' (':' type)?
```

---

## Design Rationale

### Why `->` Instead of `=>`?

| Aspect | `->` | `=>` |
|--------|------|------|
| **Functional heritage** | Haskell, OCaml, Rust | TypeScript, JavaScript |
| **Consistency** | Same as match branches | Different from match |
| **Visual weight** | Lighter, less noise | Heavier |
| **Semantics** | "maps to" / "produces" | "implies" / "arrow" |
| **Core language fit** | Functional core | OO influence |

**Decision: `->` everywhere** - functions, types, and pattern matching.

### Why OCaml-Style Match?

```
-- OCaml-style (CHOSEN)
match x {
| A -> e
| B -> e
}

-- TS-style (rejected)
match(x) {
  case A: => e
  case B: => e
}
```

**Benefits:**
1. **No parentheses** - `match x` not `match(x)` (no ambiguity without space application)
2. **No `case` keyword** - Less noise, `|` is clear delimiter
3. **Same `->`** - Consistent with functions
4. **Visual clarity** - Each pattern on its own line with `|`

### Why `type` Instead of `data`?

```
-- Haskell-style (confusing)
data Option a = Some a | None

-- TypeScript-style (CLEARER)
type Option<A> {
| Some(A)
| None()
}
```

**Benefits:**
1. **Familiar** - TypeScript devs know `type`
2. **Clearer** - `data` is ambiguous (data vs. type)
3. **Consistent** - Both languages use `type`

### Why Guards in Core?

```
-- With guards
match n {
| x if x > 0 -> "positive"
| x if x < 0 -> "negative"
| _ -> "zero"
}

-- Core AST
Case(
  PVar("x"),
  Some(App(App(Var(">"), Var("x")), Lit(0))),  -- guard
  Lit("positive")
)
```

**Benefits:**
1. **Explicit** - Guard is visible in AST
2. **Type checking** - Guard must be `Bool`
3. **Exhaustiveness** - Guarded cases are "partial"
4. **Error messages** - Can show which guard failed
5. **Optimization** - Can hoist guards out of match

### Why Primitive Operations?

```
-- Current (inefficient)
Var("+")(1, 2)

-- Better (efficient)
PrimOp(Add, [Lit(1), Lit(2)])
```

**Benefits:**
1. **Efficiency** - Direct CPU instructions, no function call overhead
2. **Type safety** - Primitive ops have fixed, known types
3. **Optimization** - Compiler can optimize primitives aggressively
4. **Serialization** - Compact encoding for network transfer

### Why Algebraic Effects?

```
-- Effect handling
handle computation {
| return(x) -> x
| ReadLine() -> k(getLine())
| Write(s) -> k(print(s))
}
```

**Benefits:**
1. **Composability** - Effects compose naturally
2. **Testability** - Easy to mock effects
3. **Separation** - Effect logic separate from business logic
4. **Distribution** - Effects can be handled remotely
5. **No hidden state** - All effects explicit in type

### Why No Object Terminology?

| Avoid | Use |
|-------|-----|
| `obj`, `object`, `class` | `record`, `type`, `data` |
| `method` | `function` |
| `instance` | `value`, `term` |
| `inheritance` | N/A (not supported) |
| `polymorphism` | `generics`, `parametric types` |

**Rationale:** Core language is **functional**, not object-oriented. Records are data structures, not objects with methods.

---

## Feature Completeness: Core → High-Level

### What Core Provides (100% Complete!)

| Feature | Core Support | High-Level Compilation |
|---------|-------------|----------------------|
| **Functions** | ✅ `Lam`, `Pi`, `App` | `function`, `=>` |
| **Types** | ✅ `Typ`, `Pi`, annotations | Type inference |
| **Records** | ✅ `Rcd`, `Dot` | Object literals |
| **Variants** | ✅ `Ctr`, `Match` | `type`, unions |
| **Pattern Matching** | ✅ `Match`, `Case`, guards | `match`, `switch` |
| **Let Bindings** | ✅ `let`, `let rec` | `const`, `let` |
| **Generics** | ✅ Parametric types | `<T>` syntax |
| **Dependent Types** | ✅ Pi types | Type-level computation |
| **Primitives** | ✅ `PrimOp` | Numbers, strings, ops |
| **Errors** | ✅ `Result` type | `try`/`catch` (desugared) |
| **Option** | ✅ `Option` type | Optional chaining |
| **Recursion** | ✅ `let rec` | Loops (desugared) |
| **Effects** | ✅ `Perform`, `Handle` | `async`/`await`, IO |
| **State** | ✅ State effects | Mutable state (desugared) |

### What Compiles Away (High-Level Sugar)

| High-Level Feature | Core Normalization |
|-------------------|-------------------|
| **If/else** | `Match` on `Bool` |
| **For/while loops** | Recursion (`let rec`) |
| **String interpolation** | String concatenation functions |
| **Null coalescing** | `match` on `Option` |
| **Optional chaining** | `match` on `Option` |
| **Async/await** | Effect handling (`Handle`) |
| **Modules/imports** | Namespaces (elaboration-time, erased) |
| **Type inference** | Holes filled by elaborator |
| **Method syntax** | Function application |
| **Classes** | Records + functions |
| **Inheritance** | Composition + functions |
| **Mutation** | State effects (`Perform("Put", ...)`) |

### What's Complete!

| Feature | Status | Notes |
|---------|--------|-------|
| **Letrec** | ✅ Complete | `let rec` for recursion |
| **Guards** | ✅ Complete | `Case` has optional `guard` |
| **Primitive ops** | ✅ Complete | Built-in functions for arithmetic, comparison, logic |
| **Built-in types** | ✅ Complete | `LitT(I32)`, `LitT(F64)`, etc. |
| **Effects** | ✅ Complete | `Perform`, `Handle` for IO, state, errors |
| **Builtins Registry** | ✅ Complete | `HostRegistry` with permission system |
| **Error Resilience** | ✅ Complete | Quote back structure on errors |
| **Arrays** | ⚠️ Library | Can be defined as data type |
| **Modules** | ⚠️ Elaboration | Namespaces, erased in core |
| **Type-level computation** | ⚠️ Future | Type families, type functions |
| **Implicit arguments** | ⚠️ Future | For ad-hoc polymorphism |

---

## Built-in Functions

The core language includes a set of built-in functions that can be executed during elaboration:

### Arithmetic Built-ins
```gleam
// All arithmetic operations are built-ins
add(1, 2)      // 3
sub(5, 3)      // 2
mul(2, 3)      // 6
div(10, 2)     // 5
mod(10, 3)     // 1
```

### Comparison Built-ins
```gleam
eq(1, 1)       // 1 (true)
neq(1, 2)      // 1 (true)
lt(1, 2)       // 1 (true)
lte(1, 1)      // 1 (true)
gt(2, 1)       // 1 (true)
gte(1, 1)      // 1 (true)
```

### Logical Built-ins
```gleam
and(1, 0)      // 0 (false)
or(1, 0)       // 1 (true)
not(0)         // 1 (true)
```

### Built-in Execution Model

Built-ins are executed during `infer` when all arguments are concrete values:

```gleam
// Concrete arguments - executes during infer
let x = add(1, 2)  // x = 3

// Non-concrete arguments - creates stuck built-in
let f = fn(x) { add(x, 1) }  // Creates VBuiltIn
```

### Permission System (Future)

For impure built-ins (file I/O, environment variables), a permission system will control execution:

```gleam
// Pure built-ins - always allowed
add(1, 2)

// Impure built-ins - require permissions
read_file("config.json")  // Requires AllowRead
get_env("API_KEY")        // Requires AllowEnv
```

---

## Compile-Time Evaluation (Comptime)

The `comptime` keyword marks expressions to be evaluated during compilation:

```gleam
// Compile-time constant
const CONFIG = comptime read_file("config.json")

// Compile-time computation
const FACTORIAL_5 = comptime {
  let rec factorial = fn(n) {
    match n {
      0 -> 1
      _ -> n * factorial(n - 1)
    }
  }
  factorial(5)
}
```

### Comptime vs Runtime

| Feature | Comptime | Runtime |
|---------|----------|---------|
| **When** | During compilation | During execution |
| **Access** | Full host capabilities | Sandboxed |
| **Result** | Embedded as literal | Computed value |
| **Errors** | Compile error | Runtime error |

### Use Cases

1. **Configuration**: Load and parse config files at compile time
2. **Code Generation**: Generate boilerplate code from templates
3. **Validation**: Validate data schemas at compile time
4. **Optimization**: Pre-compute expensive calculations

---

## Next Steps

1. **Implement lexer** - Tokenize this syntax ✅ Complete
2. **Implement parser** - Parse to `Term` AST ✅ Complete
3. **Implement serializer** - Convert to/from JSON ⚠️ Future
4. **Implement elaborator** - Convert to De Bruijn indices, fill holes ✅ Complete
5. **Implement type checker** - Using existing `src/core/core.gleam` ✅ Complete
6. **Implement effect system** - Runtime for `Perform`/`Handle ⚠️ Future
7. **Test with examples** - Verify syntax works ✅ Complete
8. **Benchmark parsing** - Ensure fast enough for cluster use ⚠️ Future

---

## Performance Goals

| Metric | Target | Rationale |
|--------|--------|-----------|
| Parse speed | >1MB/s | Fast cluster distribution |
| Serialize size | <2x AST | Compact for network |
| Parse errors | <100ms | Fast feedback |
| Memory | <10x AST | Efficient for large code |
| Effect handling | <1μs/op | Fast effect dispatch |
| Primitive ops | Native speed | Direct CPU instructions |

---

## Open Questions

1. **Binary format** - Custom binary or JSON + compression?
2. **Versioning** - How to handle syntax evolution?
3. **Compression** - gzip, zstd, or custom encoding?
4. **Streaming** - Parse large terms incrementally?
5. **Validation** - Schema for wire format?
6. **Effect types** - How to encode in type system?
7. **Effect handlers** - Multiple handlers or single?
8. **Primitive set** - What ops are primitives vs. library?
