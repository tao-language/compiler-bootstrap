# Core Language Syntax Plan

> **Goal**: TypeScript-like syntax with C-style application only
> **Status**: Ready for implementation
> **Date**: March 2025

---

## Design Principles

1. **C-style application only** - `f(x, y)` not `f x y`
2. **Familiar syntax** - TypeScript/JavaScript developers feel at home
3. **Simple grammar** - No ambiguity between space app and other constructs
4. **Clear precedence** - Obvious grouping without excessive parentheses
5. **Minimal boilerplate** - No unnecessary keywords

---

## Syntax Overview

### Atoms

```typescript
// Variables
x
foo
myVar

// Literals
42
3.14
"hello"

// Holes (metavariables)
?
?0

// Parenthesized expressions
(x)
((x))
```

### Application (C-style only)

```typescript
// Single argument
f(x)

// Multiple arguments (curried)
f(x, y)
// Desugars to: (f(x))(y)

// Nested application
f(g(x))
f(g(x), h(y))
```

### Lambda Abstraction

```typescript
// Single parameter
λx. x

// Multiple parameters (sugar for nested lambdas)
λx y z. x + y + z
// Desugars to: λx. λy. λz. x + y + z

// With type annotation
λ(x: Type). x
```

### Pi Types (Dependent Function Types)

```typescript
// Basic Pi type
(x: A) → B

// When x not used in B (regular function type)
(_: A) → B
A → B  // Sugar for (_: A) → B

// Multiple parameters (sugar for nested Pi)
(x: A, y: B) → C
// Desugars to: (x: A) → (y: B) → C
```

### Records

```typescript
// Record type
{x: Int, y: Int}

// Record value
{x: 1, y: 2}

// Empty record
{}

// Field access
r.x
r.field

// Nested access
r.x.y
```

### Constructors

```typescript
// Nullary constructor
Nil
True
False

// Unary constructor
Cons(1)
Some(42)

// Multiple arguments (curried application)
Cons(1, Nil)
// Desugars to: (Cons(1))(Nil)
```

### Type Annotations

```typescript
// Term annotation
x: Type
(λx. x): (A → B)
f(x): ReturnType
```

### Match Expressions

```typescript
// Basic match
match x {
  A → 1,
  B → 2
}

// With patterns
match list {
  Nil → 0,
  Cons(head, tail) → 1 + length(tail)
}

// With guards
match x {
  n if n > 0 → "positive",
  _ → "zero"
}
```

### Patterns

```typescript
// Wildcard
_

// Variable binding
x

// As-pattern
x @ pattern

// Constructor pattern
Cons(head, tail)
Some(x)

// Literal pattern
42
"hello"

// Record pattern
{x, y}
```

### Built-in Calls

```typescript
// Arithmetic
add(1, 2)
sub(5, 3)

// Comparison
eq(1, 1)
lt(1, 2)

// Comptime
comptime add(1, 2)
```

---

## Precedence and Associativity

### Precedence Table (highest to lowest)

| Prec | Operator/Syntax | Assoc | Example |
|------|-----------------|-------|---------|
| 100 | Atom | - | `x`, `42`, `λx. x` |
| 95 | Field access | Left | `r.x.y` |
| 90 | Constructor app | Left | `Cons(1, Nil)` |
| 85 | C-style app | Left | `f(x, y)` |
| 75 | Type annotation | Right | `x: A: B` |
| 70 | Lambda | Right | `λx. λy. x` |
| 65 | Pi type | Right | `(x: A) → (y: B) → C` |
| 60 | Match | - | `match x { ... }` |

### Examples

```typescript
// Application
f(x)(y)      // = (f(x))(y)
f(g(x))      // = f(g(x))
f(x, y)(z)   // = (f(x, y))(z)

// Lambda vs application
λx. f(x)     // = λx. (f(x))
(λx. f)(x)   // = ((λx. f)(x))

// Type annotation
f(x): T      // = (f(x)): T
f(x: T)      // = f((x: T))
```

---

## Grammar Rules (EBNF)

```ebnf
Expr = Atom
     | Expr "(" [ExprList] ")"     -- C-style application
     | Expr "." Ident              -- Field access
     | Expr ":" Type               -- Type annotation
     | "λ" LambdaParams "." Expr   -- Lambda
     | PiParams "→" Expr           -- Pi type
     | "match" Expr MatchBody      -- Match
     | "comptime" Expr             -- Comptime
     ;

Atom = Ident
     | Number
     | String
     | "?" [Ident]                 -- Hole
     | Constructor
     | "{" [FieldList] "}"         -- Record
     | "(" Expr ")"                -- Parenthesized
     | "_"                         -- Wildcard
     ;

LambdaParams = Ident
             | "(" Ident ("," Ident)* ")"
             | "(" Ident ":" Type ("," Ident ":" Type)* ")"
             ;

PiParams = "(" Ident ":" Type ")"
         | "(" Ident ":" Type ("," Ident ":" Type)* ")"
         ;

MatchBody = "{" CaseList "}"
          | "with" "{" CaseList "}"
          ;

CaseList = Case ("," Case)*
         ;

Case = Pattern ("if" Expr)? "→" Expr
     ;

Pattern = "_"                     -- Wildcard
        | Ident ("@" Pattern)?    -- Variable / As-pattern
        | Constructor "(" [PatternList] ")"
        | Number
        | String
        | "{" [FieldPatternList] "}"
        ;

ExprList = Expr ("," Expr)*
         ;

FieldList = Field ("," Field)*
          ;

Field = Ident ":" Expr
      ;

Type = Ident
     | Type "→" Type
     | "{" TypeFieldList "}"
     | "(" Type ")"
     ;

TypeFieldList = TypeField ("," TypeField)*
              ;

TypeField = Ident ":" Type
          ;
```

---

## Lexer Tokens

```
// Literals
Ident       [a-zA-Z_][a-zA-Z0-9_]*
Number      [0-9]+(\.[0-9]+)?
String      \"([^\"\\]|\\.)*\"

// Keywords
λ           Unicode lambda
fn          Function keyword
match       Match keyword
with        With keyword (optional)
if          Guard keyword
comptime    Comptime keyword
return      Return type keyword
Type        Universe type
I32, I64    Literal types
F32, F64

// Operators and punctuation
→           Arrow (Pi type)
:           Colon (type annotation)
.           Dot (field access)
,           Comma (separator)
( )         Parentheses
{ }         Braces
?           Hole
@           As-pattern
_           Wildcard
```

---

## Implementation Plan

### Phase 1: Minimal Grammar (Atoms + Application)

**Grammar rules:**
- `Expr` → `Atom` | `App`
- `Atom` → `Ident` | `Number` | `Hole` | `Paren`
- `App` → `Atom ( ExprList )`

**Constructors:**
- `make_var(token)` → `Term(Var(name), span)`
- `make_lit(token)` → `Term(Lit(value), span)`
- `make_hole(token)` → `Term(Hole(id), span)`
- `make_app(fun, args)` → `Term(App(fun, arg), span)` (fold for multiple args)

**Tests:**
- Parse variable: `x`
- Parse number: `42`
- Parse hole: `?`
- Parse application: `f(x)`
- Parse nested app: `f(g(x))`
- Parse multi-arg: `f(x, y)`

### Phase 2: Lambda and Pi Types

**Grammar rules:**
- `Expr` → `Lambda` | `PiType` | ...
- `Lambda` → `λ LambdaParams . Expr`
- `PiType` → `( Ident : Type ) → Type`

**Constructors:**
- `make_lambda(params, body)` → Nested `Term(Lam(name, body), span)`
- `make_pi(name, in_, out)` → `Term(Pi(name, in_, out), span)`

**Tests:**
- Parse lambda: `λx. x`
- Parse multi-param lambda: `λx y. x + y`
- Parse Pi type: `(x: A) → B`
- Parse arrow type: `A → B`

### Phase 3: Records and Field Access

**Grammar rules:**
- `Atom` → `Record` | `Dot`
- `Record` → `{ FieldList }`
- `Dot` → `Atom . Ident`

**Constructors:**
- `make_record(fields)` → `Term(Rcd(fields), span)`
- `make_dot(obj, field)` → `Term(Dot(obj, field), span)`

**Tests:**
- Parse record: `{x: 1, y: 2}`
- Parse field access: `r.x`
- Parse nested access: `r.x.y`

### Phase 4: Type Annotations

**Grammar rules:**
- `Expr` → `App : Type`

**Constructors:**
- `make_annotation(term, typ)` → `Term(Ann(term, typ), span)`

**Tests:**
- Parse annotation: `x: Int`
- Parse annotated app: `f(x): Int`

### Phase 5: Match Expressions

**Grammar rules:**
- `Expr` → `match Expr MatchBody`
- `MatchBody` → `{ CaseList }`
- `Case` → `Pattern → Expr`

**Constructors:**
- `make_match(arg, motive, cases)` → `Term(Match(arg, motive, cases), span)`

**Tests:**
- Parse match: `match x {A → 1}`
- Parse with patterns: `match x {Cons(h, t) → h}`

### Phase 6: Constructors

**Grammar rules:**
- `Atom` → `Constructor`
- `Constructor` → `Ident ( [ExprList] )`

**Constructors:**
- `make_constructor(name, args)` → `Term(Ctr(name, arg), span)`

**Tests:**
- Parse nullary: `Nil`
- Parse unary: `Cons(1)`
- Parse multi-arg: `Cons(1, Nil)`

### Phase 7: Comptime

**Grammar rules:**
- `Expr` → `comptime Expr`

**Constructors:**
- `make_comptime(expr)` → `Term(Comptime(expr), span)`

**Tests:**
- Parse comptime: `comptime add(1, 2)`

### Phase 8: Formatter

**Functions:**
- `format_term(term, parent_prec)` → `Doc`
- `format_atom(term)` → `Doc`
- `format_lambda(name, body, parent_prec)` → `Doc`
- `format_app(fun, args, parent_prec)` → `Doc`
- etc.

**Tests:**
- Format variable: `x`
- Format application: `f(x)`
- Format lambda: `λx. x`
- Round-trip: `parse(format(parse(s))) == parse(s)`

---

## Example Grammar Definition

```gleam
pub fn core_grammar() -> Grammar(Term) {
  use g <- grammar.define

  g
  |> grammar.name("Core")
  |> grammar.start("Expr")
  
  // Tokens
  |> grammar.token("Ident")
  |> grammar.token("Number")
  |> grammar.token("Lambda")
  |> grammar.token("Arrow")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.token("Comma")
  |> grammar.token("Dot")
  |> grammar.token("Colon")
  |> grammar.token("Question")
  |> grammar.token("LBrace")
  |> grammar.token("RBrace")
  
  // Keywords
  |> grammar.keyword("λ")
  |> grammar.keyword("fn")
  |> grammar.keyword("match")
  |> grammar.keyword("with")
  |> grammar.keyword("comptime")
  |> grammar.keyword("Type")
  |> grammar.keyword("I32")
  
  // Main expression rule (lowest precedence first)
  |> grammar.rule("Expr", [
    grammar.alt(grammar.ref("Comptime"), unwrap),
    grammar.alt(grammar.ref("Match"), unwrap),
    grammar.alt(grammar.ref("PiType"), unwrap),
    grammar.alt(grammar.ref("Lambda"), unwrap),
    grammar.alt(grammar.ref("Annotation"), unwrap),
    grammar.alt(grammar.ref("App"), unwrap),
    grammar.alt(grammar.ref("Atom"), unwrap),
  ])
  
  // Comptime: comptime expr
  |> grammar.rule("Comptime", [...])
  
  // Match: match expr { cases }
  |> grammar.rule("Match", [...])
  
  // Pi type: (x: A) → B
  |> grammar.rule("PiType", [...])
  
  // Lambda: λx. body
  |> grammar.rule("Lambda", [...])
  
  // Annotation: expr : type
  |> grammar.rule("Annotation", [...])
  
  // Application: f(x, y)
  |> grammar.rule("App", [...])
  
  // Atoms
  |> grammar.rule("Atom", [...])
}
```

---

## Summary

This simplified syntax provides:

1. **Familiarity** - TypeScript developers feel at home
2. **Simplicity** - C-style application only, no ambiguity
3. **Clarity** - Obvious precedence and grouping
4. **Expressiveness** - Full dependent type syntax
5. **Conciseness** - Minimal boilerplate

The grammar system supports all these constructs. Implementation is a matter of defining the grammar rules and constructor functions following the patterns in the calculator example.
