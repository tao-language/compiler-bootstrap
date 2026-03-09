# Core Language Implementation Status

> **Status**: Grammar system complete, core language grammar pending
> **Date**: March 2025

---

## Completed ✅

### Syntax Library (`src/syntax/`)

A complete, layout-aware grammar system with:

1. **Lexer** (`syntax/lexer.gleam`)
   - Tokenizes identifiers, keywords, numbers, strings
   - Handles comments (line and block)
   - Tracks positions for error reporting
   - Supports Unicode (λ character)

2. **Grammar DSL** (`syntax/grammar.gleam`)
   - `FormatterConfig` - Global settings (width, indent)
   - `LayoutHint` - Per-item hints (SoftBreak, HardBreak, Space, NoSeparator)
   - `OperatorLayout` - Operator formatting config
   - `SeqWithLayout` - Sequences with layout hints between elements
   - All pattern types: Token, Keyword, Ref, Seq, Choice, Opt, Many, Sep1, Parens

3. **Parser**
   - `parse_pattern()` - Dispatches on pattern type
   - `parse_seq_with_layout()` - Parses sequences with hints
   - `parse_left_assoc()` - Left-associative operator parsing
   - Error handling with position tracking

4. **Formatter**
   - `format_binary_op()` - Formats binary ops with layout
   - `format_sequence_with_layout()` - Formats sequences with hints
   - Precedence-based parenthesization
   - Soft/hard line breaks

5. **Tests** - 238 tests passing
   - Parser tests
   - Formatter tests  
   - Round-trip tests (parse → format → parse)

### Calculator Example (`src/examples/calc.gleam`)

A working example demonstrating the grammar system:

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define
  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10, grammar.default_op_layout("+")),
    grammar.op("-", Sub, 10, grammar.default_op_layout("-")),
  ])
  |> grammar.left_assoc("Term", "Factor", [
    grammar.op("*", Mul, 20, grammar.default_op_layout("*")),
    grammar.op("/", Div, 20, grammar.default_op_layout("/")),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parenthesized("Expr"), fn(e) { e }),
  ])
}
```

**Features demonstrated:**
- Operator precedence
- Left-associative operators
- Parenthesized expressions
- Automatic spacing around operators
- Round-trip parsing/formatting

---

## Pending ⏳

### Core Language Grammar

The grammar system is ready, but the core language grammar definition needs to be implemented.

**Required components:**

1. **Grammar Definition** (`src/core/grammar.gleam`)
   ```gleam
   pub fn core_grammar() -> Grammar(Term) {
     // Define all core language constructs:
     // - Atoms (variables, literals, holes)
     // - Application (C-style and space-separated)
     // - Lambda (λx. body, fn(x) { body })
     // - Pi types ((x: A) → B)
     // - Records ({x: 1, y: 2})
     // - Match (match x {A → 1})
     // - Annotations (x: Type)
   }
   ```

2. **Constructor Functions**
   ```gleam
   fn make_var(token) -> Term
   fn make_lit(token) -> Term
   fn make_lambda(params, body) -> Term
   fn make_app(fun, args) -> Term
   // ... etc
   ```

3. **Formatter** (`src/core/formatter.gleam`)
   ```gleam
   pub fn format(term: Term) -> String {
     format_term(term, -1) |> formatter.render_default
   }
   
   fn format_term(term: Term, parent_prec: Int) -> Doc {
     case term.data {
       Var(name) -> formatter.text(name)
       Lam(name, body) -> format_lambda(name, body, parent_prec)
       // ... etc
     }
   }
   ```

4. **De Bruijn Conversion**
   - Parser: names → indices (requires symbol table)
   - Formatter: indices → names (requires context)

### Implementation Challenges

1. **Application Parsing**
   - C-style: `f(x, y)` - straightforward
   - Space-separated: `f x y` - needs special handling
   - Mixed: `f(x) y` - precedence matters

2. **Lambda Syntax**
   - Multiple forms: `λx. x`, `fn(x) { x }`, `(x) => x`
   - Multiple parameters: `λx y z. body`
   - Type annotations: `λ(x: A). body`

3. **Record Syntax**
   - Fields: `{x = 1}` vs `{x: 1}` (TS-like)
   - Nested: `{x: {y: 1}}`
   - Field access: `r.x.y`

4. **Pattern Matching**
   - Complex patterns: `Cons(head, tail)`
   - Guards: `n if n > 0 → "positive"`
   - Multiple cases with layout

5. **De Bruijn Indices**
   - Surface syntax uses names
   - Internal representation uses indices
   - Need conversion in both directions

---

## Recommended Implementation Order

### Phase 1: Minimal Core Grammar

Start with the simplest working subset:

1. Atoms only (variables, numbers, holes)
2. C-style application: `f(x)`
3. Lambda: `λx. body`
4. Basic tests

### Phase 2: Expand Syntax

Add more constructs:

1. Space application: `f x`
2. Pi types: `(x: A) → B`
3. Type annotations: `x: A`
4. Records: `{x: 1}`

### Phase 3: Advanced Features

Complete the language:

1. Match expressions
2. All pattern types
3. Constructors
4. Field access

### Phase 4: Polish

Final touches:

1. De Bruijn conversion
2. Error messages
3. Performance optimization
4. Documentation

---

## Example: Minimal Core Grammar

Here's what a minimal core grammar might look like:

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

## Summary

**What's working:**
- ✅ Complete grammar system with layout support
- ✅ 238 tests passing
- ✅ Calculator example demonstrates all features
- ✅ Ready for core language implementation

**What's needed:**
- ⏳ Core language grammar definition
- ⏳ Constructor functions for all Term variants
- ⏳ Core formatter implementation
- ⏳ De Bruijn name/index conversion

**Estimated effort:**
- Minimal grammar (Phase 1): 2-4 hours
- Expanded grammar (Phase 2): 4-8 hours
- Full grammar (Phase 3): 8-16 hours
- Polish (Phase 4): 4-8 hours

The grammar system is complete and tested. Implementing the core language grammar is a matter of defining the grammar rules and constructor functions following the patterns established in the calculator example.
