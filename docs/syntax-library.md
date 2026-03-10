# Syntax Library Documentation

> **Version**: 1.0.0
> **Description**: A generic grammar DSL for building parsers with language-agnostic parser combinators, formatters, and error reporting

---

## Overview

The syntax library provides a **generic grammar DSL** that generates parsers for any AST type. The grammar is the **single source of truth** - it defines:

1. **Structure** - What to parse (patterns, tokens, keywords)
2. **Precedence** - Operator binding strength and associativity
3. **Constructors** - How to build AST from parsed values
4. **Layout** - Formatting hints for pretty-printing

### Key Features

- **Type-safe** - Grammar is parameterized by AST type (`Grammar(a)`)
- **Composable** - Build complex parsers from simple combinators
- **Operator precedence** - Built-in support for left/right-associative operators
- **Layout hints** - Soft/hard line breaks for pretty-printing
- **Error handling** - Position tracking for error messages
- **Error reporting** - Source snippets with error highlights
- **Formatter combinators** - 16+ combinators for easy formatter implementation

### Module Structure

```
src/syntax/
├── grammar.gleam         # Grammar DSL (~950 lines)
├── lexer.gleam           # Tokenizer (~400 lines)
├── formatter.gleam       # Document algebra formatter (~440 lines)
├── source_snippet.gleam  # Source snippet formatter (~260 lines)
└── error_reporter.gleam  # Error to diagnostic conversion (~220 lines)
```

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

### 6. Report Errors with Source Snippets

```gleam
// mylang/error_handler.gleam
import syntax/error_reporter
import syntax/source_snippet

pub fn handle_parse_error(error: grammar.ParseError, source: String, file: String) -> String {
  let diagnostic = error_reporter.parse_error_to_diagnostic(error, source, file)
  source_snippet.format_diagnostic(diagnostic, source)
}

// Output:
// error[E0001]: Unexpected token
//    ┌─ src/file.mylang:3:5
//    │
//  3 │ 1 + * 3
//    │     ^
//    │
//    = Expected: expression
//    = Got: *
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

/// Parse source code with grammar
pub fn parse(grammar: Grammar(a), source: String) -> ParseResult(a)
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

/// Create an alternative with explicit deconstructor
pub fn alt_with_deconstructor(
  pattern: Pattern(a),
  constructor: fn(List(Value(a))) -> a,
  deconstructor: fn(a) -> List(Value(a)),
  formatter: fn(a, Int) -> Doc,
) -> Alternative(a)
```

**Note**: The `deconstructor` is currently a stub (panics if called). It's intended for future automatic formatter generation.

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

pub type LayoutStyle {
  Inline
  BreakAfterOperator(indent: Int)
  BreakBeforeOperator(indent: Int)
  Block(open: String, close: String, indent: Int)
}

pub type OperatorLayout {
  OperatorLayout(
    separator: String,
    break_before: Bool,
    break_after: Bool,
    indent_rhs: Bool,
  )
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

/// Create operator with default layout (break after operator, indent RHS)
pub fn default_op_layout(separator: String) -> OperatorLayout

/// Create operator with break-before layout (like Haskell's $)
pub fn break_before_op_layout(separator: String) -> OperatorLayout

/// Create operator with compact layout (never break)
pub fn compact_op_layout(separator: String) -> OperatorLayout

/// Create operator with custom layout
pub fn op_with_layout(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
  layout: OperatorLayout,
) -> Operator(a)

/// Create operator with default layout
pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
  layout: OperatorLayout,
) -> Operator(a)
```

### Metadata Extraction (for Formatters)

```gleam
/// Extract operator precedence table from grammar
///
/// Returns a function that can lookup precedence by operator name
pub fn extract_precedence_table(grammar: Grammar(a)) -> fn(String) -> Result(Int, Nil)

/// Extract operator layout table from grammar
///
/// Returns a function that can lookup layout by operator name
pub fn extract_layout_table(grammar: Grammar(a)) -> fn(String) -> Result(OperatorLayout, Nil)

/// Extract constructor precedence from grammar
///
/// Returns a function that can lookup precedence by constructor name
pub fn extract_constructor_precedence(
  grammar: Grammar(a),
  constructor_map: Dict(String, String),
) -> fn(String) -> Result(Int, Nil)
```

---

## Formatter Combinators

The formatter library provides 16+ combinators that reduce boilerplate:

### Binary Operators

```gleam
/// Format binary operator with automatic precedence handling
pub fn format_binop_auto(
  format_fn: fn(a, Int) -> Doc,  // Recursive formatter
  left: a,
  right: a,
  separator: String,
  prec: Int,
  parent_prec: Int,
) -> Doc

// Example usage:
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Add(l, r) ->
      format_binop_auto(
        format_expr,
        l,
        r,
        "+",
        10,  // Precedence from grammar
        parent_prec,
      )
  }
}
```

### Unary Operators

```gleam
/// Format unary operator (prefix)
pub fn format_unary(op: String, operand: Doc) -> Doc

/// Format unary operator (postfix)
pub fn format_unary_postfix(operand: Doc, op: String) -> Doc

// Example usage:
format_unary("-", format_expr(operand, 90))  // -x
format_unary_postfix(format_expr(operand, 90), "!")  // x!
```

### Wrapped Expressions

```gleam
/// Format wrapped expression (parens, braces, brackets, etc.)
pub fn format_wrapped(open: String, content: Doc, close: String) -> Doc

// Example usage:
format_wrapped("(", format_expr(inner, 0), ")")
format_wrapped("{", format_fields(fields), "}")
```

### Lists

```gleam
/// Format list of items with separator
pub fn format_list(items: List(Doc), sep: Doc) -> Doc

// Example usage:
format_list(
  [format_expr(a, 0), format_expr(b, 0), format_expr(c, 0)],
  formatter.concat([formatter.text(","), formatter.line()]),
)
```

### Function Application

```gleam
/// Format function application
pub fn format_application(fun: Doc, args: List(Doc)) -> Doc

// Example usage:
format_application(
  format_expr(fun, 85),
  [format_expr(arg1, 0), format_expr(arg2, 0)],
)
```

### Lambda Abstraction

```gleam
/// Format lambda abstraction
pub fn format_lambda(params: List(String), body: Doc) -> Doc

// Example usage:
format_lambda(["x", "y"], format_expr(body, 0))
```

### Records

```gleam
/// Format record with fields
pub fn format_record(fields: List(#(String, Doc))) -> Doc

/// Format record with automatic layout (inline or multi-line)
pub fn format_record_auto(fields: List(#(String, Doc)), width: Int) -> Doc

// Example usage:
format_record([
  #("x", format_expr(x, 0)),
  #("y", format_expr(y, 0)),
])

// Auto-layout tries inline first, then breaks if too long
format_record_auto([
  #("x", format_expr(x, 0)),
  #("y", format_expr(y, 0)),
], 80)
```

### Match Expressions

```gleam
/// Format match expression
pub fn format_match(scrutinee: Doc, cases: List(Doc)) -> Doc

/// Format single match case
pub fn format_case(pattern: Doc, guard: Option(Doc), body: Doc) -> Doc

// Example usage:
format_match(
  format_expr(scrutinee, 85),
  [
    format_case(format_pattern(pattern1), None, format_expr(body1, 0)),
    format_case(format_pattern(pattern2), Some(format_expr(guard, 0)), format_expr(body2, 0)),
  ],
)
```

### Layout Strategies

```gleam
/// Format inline (no breaks)
pub fn format_inline(format_fn: fn(a) -> Doc, value: a) -> Doc

/// Format with soft breaks (break if needed)
pub fn format_soft_break(format_fn: fn(a) -> Doc, value: a) -> Doc

/// Format with hard breaks (always break)
pub fn format_hard_break(format_fn: fn(a) -> Doc, value: a) -> Doc

// Example usage:
format_inline(format_expr, expr)  // Try to fit on one line
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

## Error Reporting

### Parse Error to Diagnostic

```gleam
import syntax/error_reporter
import syntax/source_snippet

pub fn handle_parse_error(error: grammar.ParseError, source: String, file: String) -> String {
  let diagnostic = error_reporter.parse_error_to_diagnostic(error, source, file)
  source_snippet.format_diagnostic(diagnostic, source)
}

// Output:
// error[E0001]: Unexpected token
//    ┌─ src/file.mylang:3:5
//    │
//  3 │ 1 + * 3
//    │     ^
//    │
//    = Expected: expression
//    = Got: *
```

### Type Error to Diagnostic

```gleam
pub fn handle_type_error(error: core.TypeError, source: String, file: String) -> String {
  let diagnostic = error_reporter.type_error_to_diagnostic(error, source, file)
  source_snippet.format_diagnostic(diagnostic, source)
}

// Output:
// error[E0101]: Type mismatch
//    ┌─ src/file.mylang:5:10
//    │
//  5 │ (x : $I32) -> x
//    │     ^^^^^
//    │
//    = expected: $Type
//    = got:      $I32
```

### Diagnostic Structure

```gleam
pub type Diagnostic {
  Diagnostic(
    code: String,           // e.g., "E0001", "E0101"
    severity: Severity,     // Error, Warning, Info
    message: String,
    primary_span: Span,
    spans: List(Highlight), // Additional highlighted spans
    notes: List(String),    // Additional notes
    hints: List(String),    // Hints for fixing
  )
}
```

### Error Codes

| Code | Description |
|------|-------------|
| E0001 | Unexpected token (parse error) |
| E0101 | Type mismatch |
| E0102 | Undefined variable |
| E0103 | Not a function |
| E0104 | Arity mismatch |
| E0105 | Constructor undefined |
| E0106 | Unsolved hole |
| E0201 | Match missing case |
| E0202 | Match redundant case |
| E0301 | Comptime permission denied |

---

## Best Practices

1. **Keep grammar declarative** - Define what to parse, not how
2. **Use precedence levels** - Higher number = tighter binding
3. **Provide formatters** - Each alternative needs a formatter function (even if stub)
4. **Test round-trips** - Verify parse → format → parse produces same AST
5. **Use layout hints** - `SoftBreak` for optional line breaks
6. **Use metadata extraction** - Extract precedence from grammar for formatters
7. **Use formatter combinators** - 16+ combinators reduce boilerplate by 70-80%
8. **Report errors with snippets** - Use `error_reporter` and `source_snippet` modules

---

## Examples

### Calculator Language

See `src/examples/calc.gleam` for a complete working example with:
- Addition, subtraction, multiplication, division
- Operator precedence (* and / bind tighter than + and -)
- Left-associative operators
- Parenthesized expressions
- Round-trip testing (parse → format → parse)
- Grammar-derived formatter with metadata-aware combinators

---

## Implementation Notes

### Deconstructor Stub

The `deconstructor` field in `Alternative` is currently a stub:

```gleam
deconstructor: fn(_) { panic as "Deconstructor not implemented" }
```

It's intended for future automatic formatter generation. For now, each language implements manual formatters using the 16+ provided combinators.

### Layout Configuration

The default operator layout breaks after the operator and indents the RHS:

```gleam
pub fn default_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(
    separator: separator,
    break_before: False,
    break_after: False,  // Currently not used
    indent_rhs: False,   // Currently not used
  )
}
```

Layout breaking features (`break_before`, `break_after`, `indent_rhs`) are defined but not yet fully implemented in the formatter.

### Metadata Extraction

The metadata extraction API allows formatters to get precedence and layout information from the grammar:

```gleam
let precedence_table = grammar.extract_precedence_table(mylang_grammar())
case precedence_table("add") {
  Ok(prec) -> // Use precedence
  Error(_) -> // Operator not found
}
```

This ensures precedence is defined ONCE in the grammar and reused by the formatter.

---

## Related Documents

- **[plans/syntax/01-overview.md](plans/syntax/01-overview.md)** - Grammar system overview
- **[plans/syntax/08-grammar-derived-formatter-plan.md](plans/syntax/08-grammar-derived-formatter-plan.md)** - Grammar-derived formatter implementation (COMPLETE)
- **[plans/core/01-overview.md](plans/core/01-overview.md)** - Core language status
- **[docs/core.md](docs/core.md)** - Core language specification

---

## References

- [Grammar Implementation](src/syntax/grammar.gleam)
- [Lexer Implementation](src/syntax/lexer.gleam)
- [Formatter Implementation](src/syntax/formatter.gleam)
- [Error Reporter Implementation](src/syntax/error_reporter.gleam)
- [Source Snippet Implementation](src/syntax/source_snippet.gleam)
- [Calculator Example](src/examples/calc.gleam)
