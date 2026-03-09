# Core Language Implementation Analysis

> **Status**: Grammar system ready, core language grammar needs implementation
> **Date**: March 2025

---

## Current Implementation Status

### ✅ Complete and Working

1. **Lexer** - Tokenizes all core language tokens:
   - Identifiers and keywords (λ, Type, I32, etc.)
   - Numbers (integers and floats)
   - Strings with escape sequences
   - Operators and punctuation
   - Comments (line and block)

2. **Grammar DSL** - Full layout-aware grammar definition:
   - `FormatterConfig` - Global settings (width, indent)
   - `LayoutHint` - Per-item hints (SoftBreak, HardBreak, Space, NoSeparator)
   - `OperatorLayout` - Operator formatting (separator, break positions, indent)
   - `SeqWithLayout` - Sequences with layout hints
   - All pattern types (Token, Keyword, Ref, Seq, Choice, Opt, Many, Sep1, Parens)

3. **Parser** - Handles all grammar constructs:
   - `parse_pattern()` - Dispatches on pattern type
   - `parse_seq_with_layout()` - Parses sequences with layout hints
   - `parse_left_assoc()` - Left-associative operator parsing
   - Error handling and position tracking

4. **Formatter** - Layout-aware formatting:
   - `format_binary_op()` - Formats binary operators with layout
   - `format_sequence_with_layout()` - Formats sequences with hints
   - Precedence-based parenthesization
   - Soft/hard line breaks

5. **Tests** - 238 tests passing:
   - Parser tests
   - Formatter tests
   - Round-trip tests (parse → format → parse)

---

## What's Missing for Core Language

### 1. Core Language Grammar Definition

Need to create `src/core/grammar.gleam` with:

```gleam
pub fn core_grammar() -> Grammar(Term) {
  use g <- grammar.define

  g
  |> grammar.start("Expr")
  |> grammar.token("Ident")
  |> grammar.token("Number")
  |> grammar.token("Lambda")  // λ
  |> grammar.token("Arrow")   // →
  // ... all tokens

  // Atoms
  |> grammar.rule("Atom", [
    grammar.alt(grammar.token("Ident"), fn(values) { /* Var */ }),
    grammar.alt(grammar.token("Number"), fn(values) { /* Lit */ }),
    grammar.alt(grammar.parenthesized("Expr"), fn(values) { /* just expr */ }),
    grammar.alt(grammar.seq_with_layout([
      #(grammar.token("Lambda"), NoSeparator),
      #(grammar.token("Ident"), Space),
      #(grammar.token("Dot"), NoSeparator),
      #(grammar.ref("Expr"), NoSeparator),
    ]), fn([_, name, _, body]) { Lam(name, body) }),
    // ... more atoms
  ])

  // Application (left-associative, highest precedence)
  |> grammar.left_assoc("App", "Atom", [
    grammar.op("", App, 100, grammar.default_op_layout("")),  // Space-separated
  ])

  // Type annotation
  |> grammar.rule("Ann", [
    grammar.alt(grammar.seq_with_layout([
      #(grammar.ref("App"), Space),
      #(grammar.token("Colon"), SoftBreak),
      #(grammar.ref("Type"), NoSeparator),
    ]), fn([term, _, typ]) { Ann(term, typ) }),
  ])

  // Pi types: (x : A) → B
  |> grammar.rule("Pi", [
    grammar.alt(grammar.seq_with_layout([
      #(grammar.token("LParen"), NoSeparator),
      #(grammar.token("Ident"), Space),
      #(grammar.token("Colon"), Space),
      #(grammar.ref("Type"), SoftBreak),
      #(grammar.token("RParen"), Space),
      #(grammar.token("Arrow"), SoftBreak),
      #(grammar.ref("Type"), NoSeparator),
    ]), fn([_, name, _, in_, _, _, out]) { Pi(name, in_, out) }),
  ])

  // Records: {x = 1, y = 2}
  |> grammar.rule("Record", [
    grammar.alt(grammar.seq_with_layout([
      #(grammar.token("LBrace"), HardBreak),
      #(grammar.sep1("Field", "Comma"), SoftBreak),
      #(grammar.token("RBrace"), NoSeparator),
    ]), fn([_, fields, _]) { Rcd(fields) }),
  ])

  // Match: match arg with { pattern → body }
  |> grammar.rule("Match", [
    grammar.alt(grammar.seq_with_layout([
      #(grammar.keyword("match"), Space),
      #(grammar.ref("Expr"), Space),
      #(grammar.keyword("with"), SoftBreak),
      #(grammar.token("LBrace"), HardBreak),
      #(grammar.sep1("Case", "Comma"), SoftBreak),
      #(grammar.token("RBrace"), NoSeparator),
    ]), fn([_, arg, _, _, cases, _]) { Match(arg, motive, cases) }),
  ])

  // ... more rules
}
```

### 2. Constructor/Deconstructor Functions

Need to map parsed values to `Term` constructors:

```gleam
// For each grammar alternative, need constructor
fn make_var(values: List(Value(Term))) -> Term {
  case values {
    [TokenValue(token)] -> Term(Var(token.value), token.start)
    _ -> panic as "Expected identifier"
  }
}

fn make_lit(values: List(Value(Term))) -> Term {
  case values {
    [TokenValue(token)] -> {
      let value = int.parse(token.value) |> result.unwrap(0)
      Term(Lit(I32(value)), token.start)
    }
    _ -> panic as "Expected number"
  }
}

// ... more constructors
```

### 3. Formatter for Core Language

Need to implement `format_term()` that uses grammar metadata:

```gleam
pub fn format(term: Term) -> String {
  format_term(term, -1) |> formatter.render_default
}

fn format_term(term: Term, parent_prec: Int) -> Doc {
  case term.data {
    Typ(k) -> formatter.text("Type" <> int.to_string(k))
    Lit(value) => format_literal(value)
    Var(index) => formatter.text("var" <> int.to_string(index))
    Hole(id) => formatter.text("?" <> int.to_string(id))
    Lam(name, body) => format_lambda(name, body, parent_prec)
    Pi(name, in_, out) => format_pi(name, in_, out, parent_prec)
    App(fun, arg) => format_app(fun, arg, parent_prec)
    Rcd(fields) => format_record(fields, parent_prec)
    Match(arg, motive, cases) => format_match(arg, motive, cases, parent_prec)
    // ... more cases
  }
}
```

### 4. Integration with Existing Core Module

The current `src/core/core.gleam` has:
- Type definitions (`Term`, `Value`, etc.)
- Evaluator (`eval`, `normalize`, etc.)
- Type checker (`infer`, `check`, `unify`)
- FFI/comptime support

Need to add:
- Parser module (`src/core/parser.gleam`)
- Formatter module (`src/core/formatter.gleam`)
- Grammar definition (`src/core/grammar.gleam`)

---

## Potential Issues

### 1. Application Parsing

Core language application is space-separated, not operator-based:
```
f x y z  -- means (((f x) y) z)
```

Current `left_assoc` expects explicit operators. May need:
- Special handling for whitespace-separated application
- Or treat space as implicit operator

### 2. Lambda Syntax

Lambda uses `λx. body` syntax:
- `λ` is a special token
- `.` separates parameter from body
- Need to handle Unicode λ character

### 3. Record Fields

Record fields are `name = value` pairs:
```
{x = 1, y = 2}
```

Need `sep1` with custom separator (`=` within fields, `,` between fields).

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
- Parser needs to convert names to indices
- Formatter needs to convert indices back to names (or show as indices)

---

## Recommended Implementation Order

1. **Define core grammar** (`src/core/grammar.gleam`)
   - Start with atoms (variables, literals, holes)
   - Add application
   - Add lambda
   - Add Pi types
   - Add records
   - Add match
   - Add annotations

2. **Implement parser** (`src/core/parser.gleam`)
   - Wrap `grammar.parse()` with core-specific error handling
   - Add name-to-index conversion for De Bruijn

3. **Implement formatter** (`src/core/formatter.gleam`)
   - Pattern match on `Term`
   - Use `grammar.format_binary_op()` for operators
   - Use `grammar.format_sequence_with_layout()` for sequences

4. **Test round-trip** (`test/core/parser_formatter_test.gleam`)
   - Parse → format → parse should produce same AST
   - Test all core constructs

5. **Integrate with existing code**
   - Update `main.gleam` to use new parser
   - Ensure evaluator works with parsed terms

---

## Summary

**Is anything missing from the implementation?**

The grammar system itself is complete and working. What's missing is:

1. **Core language grammar definition** - Need to define the grammar for core language syntax
2. **Constructor functions** - Need to map parsed values to `Term` constructors
3. **Core formatter** - Need to implement `format_term()` for all `Term` variants
4. **De Bruijn conversion** - Need to handle name ↔ index conversion
5. **Integration** - Need to wire up parser/formatter with existing core module

**Can this be used to implement the core language?**

**Yes**, the grammar system has all the necessary features:
- ✅ Token/keyword parsing
- ✅ Sequences with layout hints
- ✅ Binary operators with precedence
- ✅ Left-associative operators
- ✅ Parenthesized expressions
- ✅ Optional/many/sep1
- ✅ Choice/alternatives
- ✅ Layout-aware formatting
- ✅ Precedence-based parenthesization

The core language grammar will be complex (many constructs), but the grammar system supports all the necessary patterns.
