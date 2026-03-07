# Core Language Syntax Specification

> **Status**: Final - Wire format for distributed code
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

**Recommendation: Use `->`**

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
-- With -> (RECOMMENDED)
(x: Int) -> Int
match x {
| A(a) -> a
| B -> 0
}

-- With => (TS-style, rejected)
(x: Int) => Int
match x {
| A(a): => a
| B: => 0
}
```

**Decision: Use `->` everywhere** - functions, types, and pattern matching.

### Match Syntax: OCaml-Style

Since there's no space application ambiguity, we can simplify:

```
-- Before (TS-style)
match(x) {
  case A(a): => a
  case B: => 0
}

-- After (OCaml-style) - CLEANER
match x {
| A(a) -> a
| B -> 0
}
```

**Benefits:**
- No parentheses needed (no ambiguity)
- No `case` keyword (less noise)
- `|` clearly separates patterns
- Same `->` as functions (consistent)

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

### 6. **Dependent Function Types (Pi Types)**

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

### 7. **Type Annotations**

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

### 8. **Records**

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

### 9. **Type Definitions (NOT Classes)**

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

### 10. **Constructors (NOT Methods)**

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

### 11. **Pattern Matching (OCaml-Style)**

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

-- Guards
match n {
| x if x > 0 -> "positive"
| x if x < 0 -> "negative"
| _ -> "zero"
}

-- Core term:
Match(
  Var("opt"),
  Var("Int"),  -- motive
  [
    Case(PCtr("Some", PVar("x")), Var("x")),
    Case(PCtr("None", PAny), Lit(0))
  ]
)
```

### 12. **Let Bindings**

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

-- Core term:
App(
  Lam("x", Lam("y", App(App(Var("+"), Var("x")), Var("y")))),
  Lit(1)
)(Lit(2))
```

### 13. **Holes (Metavariables)**

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

### 14. **Function Definitions**

```
-- Top-level function
add(x: Int, y: Int): Int -> x + y

-- Generic function
id<A>(x: A): A -> x

-- With pattern matching
length(list): Int -> match list {
| Nil -> 0
| Cons(_, tail) -> 1 + length(tail)
}

-- Functions operate on data
map(f: (A) -> B, list: List<A>): List<B> -> match list {
| Nil -> Nil
| Cons(head, tail) -> Cons(f(head), map(f, tail))
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

### Example 2: Function Composition

```
-- Surface
compose<A, B, C>(f: (B) -> C, g: (A) -> B, x: A): C -> f(g(x))

-- Core term
Lam("compose", 
  Lam("f", 
    Lam("g", 
      Lam("x", 
        App(Var("f"), App(Var("g"), Var("x")))
      )
    )
  )
)
```

### Example 3: Option Map (Functional, NOT OO)

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

### Example 4: Vector Head (Dependent Type)

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

### Example 5: Natural Numbers

```
-- Type definition
type Nat {
| Zero()
| Succ(n: Nat)
}

-- Addition
add(m: Nat, n: Nat): Nat -> match m {
| Zero -> n
| Succ(m') -> Succ(add(m', n))
}

-- Core term for add
Lam("add",
  Lam("m",
    Lam("n",
      Match(
        Var("m"),
        Var("Nat"),
        [
          Case(PCtr("Zero", PAny), Var("n")),
          Case(PCtr("Succ", PVar("m'")), 
            Ctr("Succ", App(App(Var("add"), Var("m'")), Var("n"))))
        ]
      )
    )
  )
)
```

---

## Wire Format (JSON-like Serialization)

For network transmission, core terms serialize to JSON:

```
-- Core term
App(App(Var("add"), Lit(1)), Lit(2))

-- JSON serialization
{
  "tag": "App",
  "fun": {
    "tag": "App",
    "fun": { "tag": "Var", "name": "add" },
    "arg": { "tag": "Lit", "value": 1 }
  },
  "arg": { "tag": "Lit", "value": 2 }
}

-- Binary serialization (more compact)
[APP, [APP, [VAR, "add"], [LIT, 1]], [LIT, 2]]
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

-- Compact binary encoding
const TAGS = {
  Typ: 0, Lit: 1, LitT: 2, Var: 3, Hole: 4,
  Rcd: 5, Ctr: 6, Dot: 7, Ann: 8,
  Lam: 9, Pi: 10, App: 11, Match: 12
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
       | term ':' type                        -- Annotation
       | 'match' var (':' term)? '{' cases '}'
       | 'let' var (':' term)? '=' term ';' term
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

cases ::= ('|' pattern '->' term)+

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

## Comparison: Functional vs OO

```
-- OO Style (REJECTED)
class Counter {
  private count: int = 0;
  
  constructor(initial: int = 0) {
    this.count = initial;
  }
  
  increment(): int {
    this.count++;  -- MUTATION!
    return this.count;
  }
}

-- Functional Style (CHOSEN)
type Counter { count: Int }

Counter(initial: Int): Counter -> { count: initial }

increment(c: Counter): (Counter, Int) ->
  ({ ...c, count: c.count + 1 }, c.count + 1)  -- Immutable update
```

```
-- OO Style (REJECTED)
for (let i = 0; i < 10; i++) {
  print(i);  -- Side effect!
}

-- Functional Style (CHOSEN)
loop(i: Int): Unit -> match i < 10 {
| true -> print(i); loop(i + 1)  -- Explicit recursion
| false -> ()
}
loop(0)
```

```
-- OO Style (REJECTED)
const result = users
  .filter(u => u.age >= 18)  -- Method chaining
  .map(u => u.name)
  .join(", ");

-- Functional Style (CHOSEN)
let adults = join(
  map(
    filter(users, (u) => u.age >= 18),  -- Explicit function application
    (u) => u.name
  ),
  ", "
)
```

---

## Next Steps

1. **Implement lexer** - Tokenize this syntax
2. **Implement parser** - Parse to `Term` AST
3. **Implement serializer** - Convert to/from JSON
4. **Implement elaborator** - Convert to De Bruijn indices
5. **Test with examples** - Verify syntax works
6. **Benchmark parsing** - Ensure fast enough for cluster use

---

## Performance Goals

| Metric | Target | Rationale |
|--------|--------|-----------|
| Parse speed | >1MB/s | Fast cluster distribution |
| Serialize size | <2x AST | Compact for network |
| Parse errors | <100ms | Fast feedback |
| Memory | <10x AST | Efficient for large code |

---

## Open Questions

1. **Binary format** - Custom binary or JSON + compression?
2. **Versioning** - How to handle syntax evolution?
3. **Compression** - gzip, zstd, or custom encoding?
4. **Streaming** - Parse large terms incrementally?
5. **Validation** - Schema for wire format?
