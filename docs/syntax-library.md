# Syntax Library Documentation

> **Version**: 1.0.0
> **Description**: A generic grammar DSL for building parsers with language-agnostic parser combinators

---

## Overview

The syntax library provides a **generic grammar DSL** that generates parsers for any AST type. The grammar is the **single source of truth** - it defines:

1. **Structure** - What to parse (patterns, tokens, keywords)
2. **Precedence** - Operator binding strength and associativity
3. **Constructors** - How to build AST from parsed values
4. **Layout** - Formatting hints for pretty-printing

### Key Features

- **Type-safe** - Grammar is parameterized by AST type
- **Composable** - Build complex parsers from simple combinators
- **Operator precedence** - Built-in support for left/right/non-associative operators
- **Layout hints** - Soft/hard line breaks for pretty-printing
- **Error recovery** - Graceful error handling with position tracking

---

## Quick Start

### 1. Define Your AST

```gleam
// mylang/ast.gleam
pub type Expr {
  Int(Int)
  Add(Expr, Expr)
  Mul(Expr, Expr)
}
```

### 2. Define Your Grammar

```gleam
// mylang/grammar.gleam
import syntax/grammar
import mylang/ast.{type Expr, Add, Int, Mul}

pub fn mylang_grammar() -> grammar.Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.name("MyLang")
  |> grammar.start("Expr")
  |> grammar.token("Number")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  // Expr = Term (('+' | '*') Term)*
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10, grammar.default_op_layout("+")),
    grammar.op("*", Mul, 20, grammar.default_op_layout("*")),
  ], 10)
  // Term = Number | (Expr)
  |> grammar.rule("Term", [
    grammar.alt(
      grammar.token_pattern("Number"),
      fn(values) {
        case values {
          [TokenValue(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
          _ -> panic as "Expected number"
        }
      },
      fn(ast, _) {
        case ast {
          Int(n) -> formatter.text(int.to_string(n))
          _ -> formatter.text("<int>")
        }
      },
    ),
    grammar.alt(
      grammar.parenthesized("Expr"),
      fn(values) {
        case values {
          [ParensValue([AstValue(expr)])] -> expr
          _ -> panic as "Expected (expr)"
        }
      },
      fn(ast, prec) { format_expr(ast, prec) },
    ),
  ])
}
```

### 3. Parse Source Code

```gleam
// mylang/parser.gleam
import syntax/grammar
import mylang/grammar

pub fn parse(source: String) -> grammar.ParseResult(Expr) {
  grammar.parse(mylang_grammar(), source)
}
```

### 4. Format AST Back to Source

```gleam
// mylang/formatter.gleam
import syntax/formatter.{type Doc}
import syntax/formatter
import mylang/ast.{type Expr, Add, Int, Mul}

pub fn format(ast: Expr) -> String {
  format_expr(ast, -1) |> formatter.render_default
}

fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_binop(format_expr(l, 10), format_expr(r, 11), " + ", 10, parent_prec)
    Mul(l, r) -> format_binop(format_expr(l, 20), format_expr(r, 21), " * ", 20, parent_prec)
  }
}

fn format_binop(left: Doc, right: Doc, op: String, prec: Int, parent_prec: Int) -> Doc {
  let doc = formatter.concat([left, formatter.text(op), right])
  case prec < parent_prec {
    True -> formatter.parens(doc)
    False -> doc
  }
}
```

### 5. Round-Trip Test

```gleam
// Test that parse → format → parse produces the same AST
let source = "1 + 2 * 3"
let result = parse(source)
let formatted = format(result.ast)
let result2 = parse(formatted)
// result.ast == result2.ast ✓
```

---

## Grammar Definition API

### Basic Functions

```gleam
/// Start defining a grammar
pub fn define(fn(GrammarBuilder(a)) -> GrammarBuilder(a)) -> Grammar(a)

/// Set grammar name (for error messages)
pub fn name(builder: GrammarBuilder(a), name: String) -> GrammarBuilder(a)

/// Set start rule
pub fn start(builder: GrammarBuilder(a), rule: String) -> GrammarBuilder(a)

/// Declare a token kind
pub fn token(builder: GrammarBuilder(a), kind: String) -> GrammarBuilder(a)

/// Declare a keyword
pub fn keyword(builder: GrammarBuilder(a), kw: String) -> GrammarBuilder(a)
```

### Rule Definition

```gleam
/// Add a basic rule with alternatives
pub fn rule(
  builder: GrammarBuilder(a),
  name: String,
  alternatives: List(Alternative(a)),
) -> GrammarBuilder(a)

/// Create an alternative with constructor and formatter
pub fn alt(
  pattern: Pattern(a),
  constructor: fn(List(Value(a))) -> a,
  formatter: fn(a, Int) -> Doc,
) -> Alternative(a)
```

### Pattern Helpers

```gleam
/// Match a token by kind
pub fn token_pattern(kind: String) -> Pattern(a)

/// Match a keyword by value
pub fn keyword_pattern(value: String) -> Pattern(a)

/// Reference another rule
pub fn ref(rule: String) -> Pattern(a)

/// Sequence of patterns
pub fn seq(patterns: List(Pattern(a))) -> Pattern(a)

/// Sequence with layout hints (for pretty-printing)
pub fn seq_with_layout(items: List(#(Pattern(a), LayoutHint))) -> Pattern(a)

/// Choice between alternatives
pub fn choice(alts: List(Pattern(a))) -> Pattern(a)

/// Optional pattern
pub fn opt(pattern: Pattern(a)) -> Pattern(a)

/// Zero or more repetitions
pub fn many(pattern: Pattern(a)) -> Pattern(a)

/// One or more, separated by separator
pub fn sep1(item: Pattern(a), sep: Pattern(a)) -> Pattern(a)

/// Parenthesized expression
pub fn parenthesized(rule_name: String) -> Pattern(a)
```

### Layout Hints

```gleam
pub type LayoutHint {
  SoftBreak     // Space when flat, newline+indent when broken
  HardBreak     // Always newline+indent
  Space         // Always space
  NoSeparator   // No separator
}
```

### Operator Helpers

```gleam
/// Add left-associative operator rule
pub fn left_assoc(
  builder: GrammarBuilder(a),
  name: String,
  first_rule: String,
  operators: List(Operator(a)),
  precedence: Int,
) -> GrammarBuilder(a)

/// Add right-associative operator rule
pub fn right_assoc(
  builder: GrammarBuilder(a),
  name: String,
  first_rule: String,
  operators: List(Operator(a)),
  precedence: Int,
) -> GrammarBuilder(a)

/// Create operator with default layout
pub fn default_op_layout(separator: String) -> OperatorLayout

/// Create operator with break-before layout (like Haskell's $)
pub fn break_before_op_layout(separator: String) -> OperatorLayout
```

---

## Common Rule Patterns

### Binary Operators (Left-Associative)

```gleam
// a + b + c = ((a + b) + c)
grammar.left_assoc("Expr", "Term", [
  grammar.op("+", Add, 10, grammar.default_op_layout("+")),
  grammar.op("-", Sub, 10, grammar.default_op_layout("-")),
], 10)
```

### Binary Operators (Right-Associative)

```gleam
// a ^ b ^ c = (a ^ (b ^ c))
grammar.right_assoc("Expr", "Factor", [
  grammar.op("^", Pow, 30, grammar.default_op_layout("^")),
], 30)
```

### Parenthesized Expressions

```gleam
grammar.alt(
  grammar.parenthesized("Expr"),
  fn(values) {
    case values {
      [ParensValue([AstValue(expr)])] -> expr
      _ -> panic as "Expected (expr)"
    }
  },
  fn(ast, prec) {
    formatter.concat([
      formatter.text("("),
      format_expr(ast, prec),
      formatter.text(")"),
    ])
  },
)
```

### Number Literals

```gleam
grammar.alt(
  grammar.token_pattern("Number"),
  fn(values) {
    case values {
      [TokenValue(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
      _ -> panic as "Expected number"
    }
  },
  fn(ast, _) {
    case ast {
      Int(n) -> formatter.text(int.to_string(n))
      _ -> formatter.text("<num>")
    }
  },
)
```

### Identifier/Variable

```gleam
grammar.alt(
  grammar.token_pattern("Ident"),
  fn(values) {
    case values {
      [TokenValue(token)] -> Var(token.value)
      _ -> panic as "Expected identifier"
    }
  },
  fn(ast, _) {
    case ast {
      Var(name) -> formatter.text(name)
      _ -> formatter.text("<var>")
    }
  },
)
```

### Sequence with Layout

```gleam
// Function call: f(a, b, c)
grammar.alt(
  grammar.seq_with_layout([
    #(grammar.token_pattern("Ident"), NoSeparator),
    #(grammar.token_pattern("LParen"), NoSeparator),
    #(grammar.sep1(grammar.ref("Arg"), grammar.token_pattern("Comma")), SoftBreak),
    #(grammar.token_pattern("RParen"), NoSeparator),
  ]),
  fn(values) { /* constructor */ },
  fn(ast, _) { /* formatter */ },
)
```

---

## Parsing and Formatting

### Parse

```gleam
import syntax/grammar

let grammar = mylang_grammar()
let result = grammar.parse(grammar, "1 + 2 * 3")

case result {
  ParseResult(ast, errors) -> {
    // ast: Expr
    // errors: List(ParseError)
  }
}
```

### Format

Each language defines its own format function that pattern matches on its AST:

```gleam
pub fn format(ast: Expr) -> String {
  format_expr(ast, -1) |> formatter.render_default
}

fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_binop(format_expr(l, 10), format_expr(r, 11), " + ", 10, parent_prec)
    // ...
  }
}
```

### Precedence-Based Parenthesization

The formatter automatically adds parentheses when needed:

```gleam
fn format_binop(left: Doc, right: Doc, op: String, prec: Int, parent_prec: Int) -> Doc {
  let doc = formatter.concat([left, formatter.text(op), right])
  case prec < parent_prec {
    True -> formatter.parens(doc)   // Need parens
    False -> doc                     // No parens needed
  }
}
```

Example:
- `format(Add(Int(1), Mul(Int(2), Int(3))))` → `"1 + 2 * 3"` (no parens)
- `format(Mul(Add(Int(1), Int(2)), Int(3)))` → `"(1 + 2) * 3"` (parens needed)

---

## Examples

### Calculator Language

See `src/examples/calc.gleam` for a complete working example.

### Lambda Calculus

```gleam
pub fn lambda_grammar() -> grammar.Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.name("Lambda")
  |> grammar.start("Expr")
  |> grammar.token("Lambda")  // λ
  |> grammar.token("Dot")     // .
  |> grammar.token("Ident")
  // Expr = App | Lam
  |> grammar.rule("Expr", [
    grammar.alt(grammar.ref("Lam"), unwrap, format_lam),
    grammar.alt(grammar.ref("App"), unwrap, format_app),
    grammar.alt(grammar.ref("Atom"), unwrap, format_atom),
  ])
  // Lam = λ Ident . Expr
  |> grammar.rule("Lam", [
    grammar.alt(
      grammar.seq([
        grammar.token("Lambda"),
        grammar.token("Ident"),
        grammar.token("Dot"),
        grammar.ref("Expr"),
      ]),
      fn(values) { /* constructor */ },
      fn(ast, _) { /* formatter */ },
    ),
  ])
  // ...
}
```

---

## Best Practices

1. **Keep grammar declarative** - Define what to parse, not how
2. **Use precedence levels** - Higher number = tighter binding
3. **Provide formatters** - Each alternative needs a formatter function
4. **Test round-trips** - Verify parse → format → parse produces same AST
5. **Use layout hints** - `SoftBreak` for optional line breaks

---

## References

- [Calculator Example](../src/examples/calc.gleam)
- [Core Language Grammar](../src/core/grammar.gleam)
- [Core Language Formatter](../src/core/formatter.gleam)
