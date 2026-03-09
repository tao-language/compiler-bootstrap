# Core Language Syntax Specification

> **Goal**: TypeScript-like syntax with C-style application only
> **Status**: Ready for implementation
> **Date**: March 2025

---

## Status

### What's Working

- Lexer tokenizes all core language tokens
- Grammar DSL with full layout support
- Parser handles all grammar constructs
- Formatter with precedence-based parenthesization
- **238 tests passing** for grammar system

### What's Pending

- Core language grammar definition (`src/core/grammar.gleam`)
- Constructor/deconstructor functions for all `Term` variants
- De Bruijn name/index conversion
- Integration with existing core module

### Implementation Phases

1. **Phase 1**: Minimal grammar (atoms + application) - 2-4 hours
2. **Phase 2**: Lambda and Pi types - 4-6 hours
3. **Phase 3**: Records and field access - 4-6 hours
4. **Phase 4**: Type annotations - 2-4 hours
5. **Phase 5**: Match expressions - 6-8 hours
6. **Phase 6**: Constructors - 2-4 hours
7. **Phase 7**: Comptime integration - 4-6 hours
8. **Phase 8**: Formatter - 6-8 hours
9. **Phase 9**: De Bruijn conversion - 4-6 hours
10. **Phase 10**: Polish - 4-8 hours

**Total estimated effort**: 34-54 hours

### Related

- See **[01-overview.md](./01-overview.md)** for overall implementation status
- See **[03-ffi-comptime.md](./03-ffi-comptime.md)** for FFI/comptime details

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

## Grammar Definition Structure

### Minimal Core Grammar (Phase 1)

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
  |> grammar.token("Dot")
  |> grammar.token("Arrow")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.token("Comma")
  |> grammar.token("Colon")
  |> grammar.token("Question")
  |> grammar.token("LBrace")
  |> grammar.token("RBrace")

  // Keywords
  |> grammar.keyword("λ")
  |> grammar.keyword("match")
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

## Implementation Phases

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

## Implementation Challenges

### 1. Application Parsing

Core language application is C-style only:
```
f(x, y)  -- means (((f x) y) for curried application
```

This is straightforward with the grammar system - just parse as left-associative sequence.

### 2. Lambda Syntax

Lambda uses `λx. body` syntax:
- `λ` is a special token (Unicode character)
- `.` separates parameter from body
- Multiple parameters: `λx y z. body` (sugar for nested lambdas)

### 3. Record Fields

Record fields are `name: value` pairs:
```
{x: 1, y: 2}
```

Use `sep1` with custom field pattern.

### 4. Pattern Matching

Match expressions have complex syntax:
```
match x with {
  A(n) → n + 1,
  B → 0
}
```

Need:
- Pattern grammar (constructors, wildcards, as-patterns)
- Case grammar (pattern → body)
- Proper layout for multi-line matches

### 5. De Bruijn Indices

Core language uses De Bruijn indices internally, but surface syntax uses names:
- Parser needs to convert names to indices (requires symbol table)
- Formatter needs to convert indices back to names (or show as indices)

---

## Modular Grammar Definition

To manage complexity, split grammar into multiple functions:

```gleam
pub fn core_grammar() -> Grammar(Term) {
  grammar.new()
  |> grammar.start("Expr")
  |> with_type_rules(_)
  |> with_term_rules(_)
  |> with_pattern_rules(_)
  |> with_case_rules(_)
}

fn with_type_rules(g: Grammar(Term)) -> Grammar(Term) {
  g
  |> grammar.rule("Type", [...])
  |> grammar.rule("PiType", [...])
}

fn with_term_rules(g: Grammar(Term)) -> Grammar(Term) {
  g
  |> grammar.rule("Expr", [...])
  |> grammar.rule("Lambda", [...])
  |> grammar.rule("App", [...])
  |> grammar.rule("Atom", [...])
}

fn with_pattern_rules(g: Grammar(Term)) -> Grammar(Term) {
  g
  |> grammar.rule("Pattern", [...])
}

fn with_case_rules(g: Grammar(Term)) -> Grammar(Term) {
  g
  |> grammar.rule("Match", [...])
  |> grammar.rule("Case", [...])
}
```

---

## Example Grammar Definition

```gleam
import syntax/grammar.{type Grammar}
import core/core.{type Term, Term, Var, Lit, Lam, App, Hole}
import core/core.{I32}
import gleam/int

pub fn core_grammar() -> Grammar(Term) {
  use g <- grammar.define

  g
  |> grammar.name("Core")
  |> grammar.start("Expr")
  |> grammar.token("Ident")
  |> grammar.token("Number")
  |> grammar.token("Lambda")
  |> grammar.token("Dot")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.token("Comma")

  // Expr = Atom | Lambda | App
  |> grammar.rule("Expr", [
    grammar.alt(grammar.ref("Lambda"), unwrap),
    grammar.alt(grammar.ref("App"), unwrap),
    grammar.alt(grammar.ref("Atom"), unwrap),
  ])

  // Lambda = λ Ident . Expr
  |> grammar.rule("Lambda", [
    grammar.alt(
      grammar.seq([
        grammar.token("Lambda"),
        grammar.token("Ident"),
        grammar.token("Dot"),
        grammar.ref("Expr"),
      ]),
      fn(values) {
        case values {
          [_, name, _, body] => make_lambda(name, body)
          _ => panic as "Invalid lambda"
        }
      },
    ),
  ])

  // App = Atom ( Expr )
  |> grammar.rule("App", [
    grammar.alt(
      grammar.seq([
        grammar.ref("Atom"),
        grammar.token("LParen"),
        grammar.ref("Expr"),
        grammar.token("RParen"),
      ]),
      fn(values) {
        case values {
          [fun, _, arg, _] => make_app(fun, arg)
          _ => panic as "Invalid app"
        }
      },
    ),
  ])

  // Atom = Ident | Number | ( Expr )
  |> grammar.rule("Atom", [
    grammar.alt(grammar.token("Ident"), make_var),
    grammar.alt(grammar.token("Number"), make_lit),
    grammar.alt(
      grammar.seq([
        grammar.token("LParen"),
        grammar.ref("Expr"),
        grammar.token("RParen"),
      ]),
      fn(values) {
        case values {
          [_, expr, _] => expr
          _ => panic as "Invalid parens"
        }
      },
    ),
  ])
}

fn unwrap(values) {
  case values {
    [AstValue(term)] => term
    _ => panic as "Expected single value"
  }
}

fn make_var(token) {
  Term(Var(token.value), token.start)
}

fn make_lit(token) {
  case int.parse(token.value) {
    Ok(n) => Term(Lit(I32(n)), token.start)
    Error(_) => Term(Lit(I32(0)), token.start)
  }
}

fn make_lambda(name_token, body) {
  Term(Lam(name_token.value, body), name_token.start)
}

fn make_app(fun, arg) {
  Term(App(fun, arg), get_span(fun, arg))
}

fn get_span(t1, t2) {
  case t1, t2 {
    Term(_, span), _ => span
  }
}
```

---

## See Also

- [Core Language Overview](./01-overview.md)
- [FFI and Comptime](./03-ffi-comptime.md)
- [Grammar DSL](../grammar/02-grammar-dsl.md)
