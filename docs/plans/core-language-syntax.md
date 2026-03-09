# Core Language Syntax Plan

> **Goal**: Familiar TypeScript-like syntax with C-style application
> **Status**: Design proposal
> **Date**: March 2025

---

## Design Principles

1. **Familiar syntax** - TypeScript/JavaScript developers should feel at home
2. **C-style application** - `f(x)` with sugar for multiple args `f(x, y, z)`
3. **Space application supported** - `f x y z` still works (for lambda calculus purists)
4. **Minimal boilerplate** - No unnecessary keywords or punctuation
5. **Clear precedence** - Obvious grouping without excessive parentheses

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
true
false

// Holes (metavariables)
?
?0
?myHole

// Parenthesized expressions
(x)
((x))
```

### Application

```typescript
// C-style with parentheses (primary)
f(x)
f(x, y)
f(x, y, z)

// Space-separated (sugar, left-associative)
f x
f x y
f x y z

// Mixed (space has lower precedence than comma)
f(x, y) z     // = (f(x, y))(z)
f x(y)        // = (f(x))(y)
```

### Lambda Abstraction

```typescript
// Single parameter
λx. x
fn(x) { x }
(x) => x

// Multiple parameters (sugar for nested lambdas)
λx y z. x + y + z
fn(x, y, z) { x + y + z }
(x, y, z) => x + y + z

// With type annotation
λ(x: Type). x
fn(x: Type) { x }
(x: Type) => x

// With return type
fn(x: A): B { body }
(x: A): B => body
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
// = (x: A) → (y: B) → C

// With explicit result type
(x: A) → (y: B x) → C x y
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
(r.x).y
```

### Constructors

```typescript
// Nullary constructor
Nil
True
False
None

// Unary constructor
Cons(1)
Some(42)
Left(error)

// Multiple arguments (curried application)
Cons(1, Nil)
// = (Cons(1))(Nil)
```

### Type Annotations

```typescript
// Term annotation
x: Type
(λx. x): (A → A)
f(x): ReturnType

// In lambda parameters
fn(x: Int) { x }
λ(x: Int). x

// In Pi types
(x: Int) → Int
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
  n if n < 0 → "negative",
  _ → "zero"
}

// With type annotation on scrutinee
match (x: Type) {
  Type0 → ...,
  Type1 → ...
}

// With motive (dependent pattern matching)
match x return (Type) {
  A → Int,
  B → Bool
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
true

// Record pattern
{x, y}
{x: xVal, y: yVal}

// Type pattern
Type0
I32
```

### Built-in Calls

```typescript
// Arithmetic
add(1, 2)
sub(5, 3)
mul(2, 3)
div(10, 2)

// Comparison
eq(1, 1)
lt(1, 2)

// Logical
and(true, false)
or(true, false)
not(false)

// Comptime
comptime add(1, 2)
comptime read_file("config.json")
```

### Comments

```typescript
// Line comment
/* Block comment */

// Nested block comments
/* outer /* inner */ outer */
```

---

## Precedence and Associativity

### Precedence Table (highest to lowest)

| Precedence | Operator/Syntax | Associativity | Example |
|------------|-----------------|---------------|---------|
| 100 | Atom | - | `x`, `42`, `λx. x` |
| 95 | Field access | Left | `r.x.y` = `(r.x).y` |
| 90 | Constructor app | Left | `Cons(1, Nil)` |
| 85 | C-style app | Left | `f(x, y)` |
| 80 | Space app | Left | `f x y` = `(f x) y` |
| 75 | Type annotation | Right | `x: A: B` = `x: (A: B)` ❌ (error) |
| 70 | Lambda | Right | `λx. λy. x` |
| 65 | Pi type | Right | `(x: A) → (y: B) → C` |
| 60 | Match | - | `match x { ... }` |

### Examples

```typescript
// Application precedence
f(x) y      // = (f(x))(y)
f x(y)      // = (f(x))(y)
f(x, y) z   // = (f(x, y))(z)

// Lambda vs application
λx. f x     // = λx. (f x)
(λx. f) x   // = ((λx. f) x)

// Pi type vs lambda
(x: A) → λy. y  // = (x: A) → (λy. y)
((x: A) → λy. y)(z)  // Application of Pi type (type error!)

// Type annotation
f(x): T       // = (f(x)): T (annotate the application)
f(x: T)       // = f((x: T)) (annotate the argument)
```

---

## Grammar Rules (EBNF)

```ebnf
Expr = Atom
     | Expr "(" [ExprList] ")"    -- C-style application
     | Expr Expr                  -- Space application
     | Expr "." Ident             -- Field access
     | Expr ":" Type              -- Type annotation
     | "λ" LambdaParams "." Expr  -- Lambda
     | "fn" LambdaParams TypeAnnotation? Block
     | LambdaParams "=>" Expr     -- Arrow function
     | PiParams "→" Expr          -- Pi type
     | "match" Expr MatchBody     -- Match
     | "comptime" Expr            -- Comptime
     ;

Atom = Ident
     | Number
     | String
     | "true" | "false"
     | "?" [Ident]                -- Hole
     | Constructor
     | "{" [FieldList] "}"        -- Record
     | "(" Expr ")"               -- Parenthesized
     ;

LambdaParams = Ident
             | "(" Ident ("," Ident)* ")"
             | "(" Ident ":" Type ("," Ident ":" Type)* ")"
             ;

PiParams = "(" Ident ":" Type ")"
         | "(" Ident ":" Type ("," Ident ":" Type)* ")"
         ;

TypeAnnotation = ":" Type
               ;

Block = "{" Expr "}"
      ;

MatchBody = "{" CaseList "}"
          | "with" "{" CaseList "}"
          ;

CaseList = Case ("," Case)*
         ;

Case = Pattern ("if" Expr)? "→" Expr
     ;

Pattern = "_"                      -- Wildcard
        | Ident ("@" Pattern)?     -- Variable / As-pattern
        | Constructor "(" [PatternList] ")"
        | Number
        | String
        | "{" [FieldPatternList] "}"
        ;

ExprList = Expr ("," Expr)*
         ;

FieldList = Field ("," Field)*
          ;

Field = Ident "=" Expr
      ;
```

---

## Layout and Formatting

### Single-line vs Multi-line

```typescript
// Short expressions stay on one line
let x = 42
let f = λx. x + 1

// Long expressions break at operators
let result = veryLongFunctionName(
  argument1,
  argument2,
  argument3
)

// Lambda with long body
let f = fn(x: VeryLongTypeName) {
  // Body indented
  x + 1
}

// Match always breaks
match value {
  Pattern1 → body1,
  Pattern2 → body2
}
```

### Indentation

- 2 spaces per level (configurable)
- Consistent indentation within blocks
- Closing brace at same indent as opening

### Line Breaking

- Break after operators (binary ops)
- Break before operators (unary ops like λ)
- Break after commas in lists
- Break after `{` in blocks

---

## Comparison with Existing Syntax

### Current Core Syntax vs New TS-like Syntax

| Concept | Current | New TS-like |
|---------|---------|-------------|
| Variable | `x` | `x` |
| Lambda | `λx. x` | `λx. x` or `fn(x) { x }` |
| Application | `f x` | `f(x)` or `f x` |
| Pi type | `(x: A) → B` | `(x: A) → B` |
| Record | `{x = 1}` | `{x: 1}` |
| Field access | `r.x` | `r.x` |
| Match | `match x with {A → 1}` | `match x {A → 1}` |
| Type annotation | `(x : A)` | `x: A` |
| Hole | `?` | `?` |

### Key Changes

1. **Record syntax**: `{x = 1}` → `{x: 1}` (TS-like)
2. **Type annotation**: `(x : A)` → `x: A` (no parens needed)
3. **Application**: `f x` → `f(x)` (C-style primary)
4. **Lambda**: `λx. x` stays, but `fn(x) { x }` added as sugar

---

## Implementation Notes

### Grammar Rules Needed

1. **Atom rule** - Variables, literals, holes, constructors
2. **Application rules** - C-style and space-separated
3. **Lambda rule** - With multiple syntax options
4. **Pi type rule** - Dependent function types
5. **Record rule** - Type and value syntax
6. **Match rule** - Pattern matching
7. **Pattern rule** - All pattern types
8. **Type rule** - All type expressions

### Lexer Tokens

```
Ident, Number, String,
λ, fn, =>, →, :, ., ,,
{, }, (, ), [, ],
match, with, if, comptime,
true, false, _, ?, @
```

### Parser Challenges

1. **Application ambiguity** - `f(x)` vs `f (x)` vs `f(x) y`
   - Solution: C-style has higher precedence than space app

2. **Lambda vs Pi type** - Both start with `(`
   - Solution: Look for `→` (Pi) vs `=>` or `{` (lambda)

3. **Record vs block** - Both use `{}`
   - Solution: Context-dependent (type context vs expr context)

4. **Constructor vs variable** - Both are identifiers
   - Solution: Capitalization convention or symbol table lookup

---

## Examples

### Identity Function

```typescript
// Lambda syntax
λx. x

// Function syntax
fn(x) { x }

// With type
fn(x: A): A { x }
λ(x: A). x
```

### Composition

```typescript
// Compose two functions
λf g x. f(g(x))

// With types
λ(f: B → C) (g: A → B) (x: A). f(g(x))

// Pi type
(f: B → C) → (g: A → B) → (x: A) → C
```

### List Length

```typescript
fn length(list) {
  match list {
    Nil → 0,
    Cons(head, tail) → 1 + length(tail)
  }
}

// With types
fn length<A>(list: List<A>): Int {
  match list {
    Nil → 0,
    Cons(_, tail) → 1 + length(tail)
  }
}
```

### Dependent Pair (Sigma Type)

```typescript
// Existential: ∃x. P x
{x: A, P(x)}

// Projection
let pair = {x: 1, proof: isPositive(1)}
pair.x      // = 1
pair.proof  // = isPositive(1)
```

### Church Numerals

```typescript
// Type
Church = λA. (A → A) → A → A

// Zero
zero = λA f x. x

// One
one = λA f x. f(x)

// Successor
succ = λn A f x. f(n(A)(f)(x))

// Addition
add = λm n A f x. m(A)(f)(n(A)(f)(x))
```

---

## Migration Path

### Phase 1: Basic Syntax

- [ ] Atoms (variables, literals, holes)
- [ ] C-style application `f(x)`
- [ ] Lambda `λx. x` and `fn(x) { x }`
- [ ] Pi types `(x: A) → B`

### Phase 2: Advanced Syntax

- [ ] Space application `f x`
- [ ] Records `{x: 1}`
- [ ] Field access `r.x`
- [ ] Constructors `Cons(1)`

### Phase 3: Pattern Matching

- [ ] Match expressions
- [ ] All pattern types
- [ ] Guards

### Phase 4: Sugar and Convenience

- [ ] Multiple lambda parameters
- [ ] Arrow function syntax
- [ ] Type annotation sugar

---

## Summary

This TS-like syntax provides:

1. **Familiarity** - TypeScript developers will feel at home
2. **Flexibility** - Both C-style `f(x)` and space `f x` application
3. **Clarity** - Obvious precedence and grouping
4. **Expressiveness** - Full dependent type syntax
5. **Conciseness** - Minimal boilerplate, sensible defaults

The grammar system supports all these constructs - it's a matter of defining the grammar rules and implementing the parser/formatter.
