# Core Language Syntax Specification

> **Goal**: TypeScript-like syntax with C-style application only
> **Status**: ⏳ In Progress - Minimal skeleton complete (4/13 Term variants), ⚠️ Tao integration changes planned
> **Date**: March 2025

---

## Status

### What's Working

- ✅ Minimal skeleton grammar with 4 Term variants
- ✅ Variables: `x` → `Var(0)`
- ✅ Literals: `42` → `Lit(I32(42))`
- ✅ Lambda: `λx. x` → `Lam("x", body)`
- ✅ Application: `f(x)` → `App(fun, arg)`
- ✅ Precedence-based parenthesization
- ✅ Round-trip tests (parse → format → parse)
- ✅ Single file: `src/core/syntax.gleam`
- **18 tests passing**

### Known Limitations

- **De Bruijn conversion** - All identifiers become `Var(0)` (no name-to-index conversion yet)
- **Limited Term coverage** - Only 4 of 13 Term variants implemented
- **Formatter uses Term pattern matching** - Not fully grammar-derived yet (format_term function)
- **Dummy spans** - All terms use `Span("input", 0, 0)` instead of real positions
  - See **[../grammar/05-source-location-tracking.md](../grammar/05-source-location-tracking.md)** for planned fix

### Tao Integration Changes Required

The following changes are needed to support the Tao high-level language:

| Change | Priority | Description | Status |
|--------|----------|-------------|--------|
| Untyped literals | HIGH | Change `Literal` to untyped `Int(Int)`, `Float(Float)` | 📋 Planned |
| Coercion term | HIGH | Add `Coerce(term, from, to)` for type coercion | 📋 Planned |
| Pattern guards | MEDIUM | Add `guard: Option(Term)` to `Case` type | 📋 Planned |
| Overload metadata | LOW | Track overloaded functions in `State` | 📋 Planned |

See **[04-tao-integration.md](./04-tao-integration.md)** for detailed integration plan.

### What's Pending

**Phase 2: Simple Terms** (can add in batch)
- [ ] `Hole` (?)
- [ ] `Typ(k)` (Type0, Type1)
- [ ] `LitT(typ)` (I32, F64)
- [ ] **Tao change**: Untyped literals

**Phase 3: Medium Complexity**
- [ ] `Ann(term, typ)` - Type annotations
- [ ] `Dot(arg, field)` - Field access
- [ ] `Ctr(tag, arg)` - Constructors
- [ ] **Tao change**: Coercion term

**Phase 4: Complex Terms** (add one at a time)
- [ ] `Pi(name, in, out)` - Dependent function types
- [ ] `Rcd(fields)` - Records
- [ ] `Match(arg, motive, cases)` - Pattern matching
- [ ] `Call(name, args)` - Built-in calls
- [ ] `Comptime(term)` - Compile-time evaluation
- [ ] **Tao change**: Pattern guards

**Phase 5: Polish**
- [ ] Proper De Bruijn name/index conversion
- [ ] Full pattern grammar (wildcards, as-patterns, constructor patterns)
- [ ] Integration with core/core evaluator and type checker

**Phase 6: Source Location Tracking**
- [ ] Update Token type with line/column
- [ ] Update Span type with start/end positions
- [ ] Add position helper functions to grammar DSL
- [ ] Update all constructors to use real positions
- See **[../grammar/05-source-location-tracking.md](../grammar/05-source-location-tracking.md)** for details

### Related

- See **[01-overview.md](./01-overview.md)** for overall implementation status
- See **[04-tao-integration.md](./04-tao-integration.md)** for Tao integration plan
- See **[03-ffi-comptime.md](./03-ffi-comptime.md)** for FFI/comptime details
- See **[../../syntax-library.md](../../syntax-library.md)** for syntax library usage

---

## Current Grammar (Minimal Skeleton)

```gleam
pub fn core_grammar() -> grammar.Grammar(Term) {
  use g <- grammar.define

  g
  |> grammar.name("Core")
  |> grammar.start("Expr")
  // Tokens
  |> grammar.token("Ident")
  |> grammar.token("Number")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.token("Lambda")
  |> grammar.token("Dot")
  // Main expression rule
  |> grammar.rule("Expr", [
    grammar.alt(grammar.ref("Lambda"), unwrap, format_term),
    grammar.alt(grammar.ref("App"), unwrap, format_term),
    grammar.alt(grammar.ref("Atom"), unwrap, format_term),
  ])
  // Lambda: λx. body
  |> grammar.rule("Lambda", [
    grammar.alt(
      grammar.seq([
        grammar.token("Lambda"),
        grammar.token("Ident"),
        grammar.token("Dot"),
        grammar.ref("Expr"),
      ]),
      make_lambda,
      format_term,
    ),
  ])
  // Application: f(x)
  |> grammar.rule("App", [
    grammar.alt(
      grammar.seq([
        grammar.ref("Atom"),
        grammar.token("LParen"),
        grammar.ref("Expr"),
        grammar.token("RParen"),
      ]),
      make_application,
      format_term,
    ),
  ])
  // Atoms
  |> grammar.rule("Atom", [
    grammar.alt(grammar.token("Ident"), make_var, format_term),
    grammar.alt(grammar.token("Number"), make_literal, format_term),
    grammar.alt(
      grammar.seq([
        grammar.token("LParen"),
        grammar.ref("Expr"),
        grammar.token("RParen"),
      ]),
      unwrap_parens,
      format_term,
    ),
  ])
}
```

---

## Full Grammar Specification (EBNF)

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
     | "?" [Ident]                 -- Hole
     | "{" [FieldList] "}"         -- Record
     | "(" Expr ")"                -- Parenthesized
     ;

LambdaParams = Ident
             | "(" Ident ("," Ident)* ")"
             ;

PiParams = "(" Ident ":" Type ")"
         ;

MatchBody = "with" "{" CaseList "}"
          ;

CaseList = Case ("," Case)*
         ;

Case = Pattern "→" Expr
     ;

Pattern = "_"                     -- Wildcard
        | Ident ("@" Pattern)?    -- Variable / As-pattern
        | Constructor "(" [PatternList] ")"
        ;

ExprList = Expr ("," Expr)*
         ;

FieldList = Field ("," Field)*
          ;

Field = Ident ":" Expr
      ;

Type = Ident
     | Type "→" Type
     | "(" Type ")"
     ;
```

---

## Implementation Pattern

Each grammar rule follows this pattern:

```gleam
grammar.alt(
  grammar.seq([/* pattern */]),
  // Constructor: values → AST
  fn(values) {
    case values {
      [/* pattern */] -> Term(Constructor(/* args */), Span("input", 0, 0))
      _ -> panic as "Expected /* name */"
    }
  },
  // Formatter: AST → Doc (via format_term pattern match)
  format_term,
)
```

---

## Formatter Implementation

The formatter pattern-matches on Term and handles precedence:

```gleam
fn format_term(term: Term, parent_prec: Int) -> formatter.Doc {
  case term.data {
    Var(index) -> formatter.concat([
      formatter.text("var"),
      formatter.text(int.to_string(index)),
    ])
    Lit(value) -> {
      case value {
        I32(n) -> formatter.text(int.to_string(n))
        _ -> formatter.text("<lit>")
      }
    }
    Lam(name, body) -> {
      let inner = formatter.concat([
        formatter.text("λ"),
        formatter.text(name),
        formatter.text(". "),
        format_term(body, 70),
      ])
      wrap_parens(inner, 70 < parent_prec)
    }
    App(fun, arg) -> {
      let inner = formatter.concat([
        format_term(fun, 85),
        formatter.text("("),
        format_term(arg, 85),
        formatter.text(")"),
      ])
      wrap_parens(inner, 85 < parent_prec)
    }
    _ -> formatter.text("<unknown>")
  }
}

fn wrap_parens(doc, condition) {
  case condition {
    True -> formatter.parens(doc)
    False -> doc
  }
}
```

### Precedence Levels

| Construct | Precedence |
|-----------|------------|
| Atoms (Var, Lit, etc.) | 100 |
| Application | 85 |
| Lambda | 70 |
| Pi type | 65 |
| Match | 60 |

Lower precedence = looser binding = more likely to need parens.

---

## Test Examples

### Parsing Tests

```gleam
pub fn parse_var_test() {
  let result = syntax.parse("x")
  result.errors |> should.equal([])
}

pub fn parse_lambda_test() {
  let result = syntax.parse("λx. x")
  result.errors |> should.equal([])
  case result.ast {
    Term(Lam(_, _), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}
```

### Formatting Tests

```gleam
pub fn format_lambda_test() {
  let body = Term(Var(0), span())
  let term = Term(Lam("x", body), span())
  syntax.format(term) |> should.equal("λx. var0")
}
```

### Round-Trip Tests

```gleam
pub fn roundtrip_lambda_test() {
  let source = "λx. x"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  // Note: produces "λx. var0" due to De Bruijn conversion
  formatted |> should.equal("λx. var0")
}
```

### Precedence Tests

```gleam
pub fn format_lambda_in_app_test() {
  // (λx. x)(42) - lambda in application needs parens
  let body = Term(Var(0), span())
  let lam = Term(Lam("x", body), span())
  let arg = Term(Lit(I32(42)), span())
  let term = Term(App(lam, arg), span())
  syntax.format(term) |> should.equal("(λx. var0)(42)")
}
```

---

## Implementation Challenges

### 1. De Bruijn Conversion

**Problem**: Surface syntax uses names (`x`), but internal representation uses indices (`Var(0)`).

**Current approach**: All identifiers become `Var(0)` (dummy index).

**Future approach**: 
- Parser: Build symbol table, convert names to indices
- Formatter: Use context to convert indices back to names

### 2. Grammar-Derived Formatting

**Current**: `format_term` pattern-matches on Term directly.

**Future**: Each grammar alternative provides its own formatter function, fully derived from grammar.

### 3. Pattern Matching Grammar

Match expressions need complex pattern grammar:
- Wildcards: `_`
- Variables: `x`
- As-patterns: `x @ Cons(h, t)`
- Constructor patterns: `Cons(h, t)`

---

## File Structure

```
src/core/
├── syntax.gleam         # Single source of truth
│   ├── core_grammar()   # Grammar definition
│   ├── parse()          # Parser (generated)
│   ├── format()         # Formatter (generated)
│   ├── Constructors     # make_lambda, make_app, etc.
│   └── Formatters       # format_term, wrap_parens, etc.
└── core.gleam           # Term types, evaluator, type checker

test/core/
├── syntax_test.gleam    # Syntax tests (18 passing)
└── core_test.gleam      # Core module tests (263 passing)
```

---

## See Also

- [Core Language Overview](./01-overview.md)
- [FFI and Comptime](./03-ffi-comptime.md)
- [Syntax Library Documentation](../../syntax-library.md)
- [Grammar DSL](../grammar/02-grammar-dsl.md)
