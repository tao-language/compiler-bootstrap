# Syntax Library Documentation

> **Version**: 2.0.0
> **Description**: A generic grammar DSL for building parsers with language-agnostic parser combinators, formatters, and error reporting
> **Updated**: March 2025 - Now with direct record construction!

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
- **Direct construction** - Simple, declarative grammar definition (no Builder pattern!)

### Module Structure

```
src/syntax/
├── grammar.gleam         # Grammar DSL (~850 lines)
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
  grammar.Grammar(
    name: "MyLang",
    start: "Expr",
    tokens: ["Number", "LParen", "RParen"],
    keywords: [],
    operators: [
      grammar.op("+", Add, 10),
      grammar.op("*", Mul, 20),
    ],
    rules: [
      // Expr = Term (('+' | '*') Term)*
      grammar.left_assoc_rule("Expr", "Term", [
        grammar.op("+", Add, 10),
        grammar.op("*", Mul, 20),
      ], 10),
      // Term = Number | (Expr)
      grammar.rule("Term", [
        grammar.alt(
          grammar.token_pattern("Number"),
          fn(values) {
            case values {
              [TokenValue(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
              _ -> panic as "Expected number"
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
        ),
      ]),
    ],
  )
}
```

### 3. Parse Source Code

```gleam
// mylang/parser.gleam
import syntax/grammar
import mylang/grammar

pub fn parse(source: String) -> grammar.ParseResult(Expr) {
  let error_ast = Int(0)  // Default value for error recovery
  grammar.parse(mylang_grammar(), source, error_ast)
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
    Add(l, r) -> format_binop(l, r, "+", 10, parent_prec)
    Mul(l, r) -> format_binop(l, r, "*", 20, parent_prec)
  }
}

fn format_binop(left: Expr, right: Expr, op: String, prec: Int, parent_prec: Int) -> Doc {
  let doc = formatter.concat([
    format_expr(left, prec),
    formatter.text(" " <> op <> " "),
    format_expr(right, prec + 1),
  ])
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

### Grammar Record

```gleam
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: List(Rule(a)),
    tokens: List(String),
    keywords: List(String),
    operators: List(Operator(a)),
  )
}
```

**Fields**:
- `name` - Grammar name (for error messages)
- `start` - Start rule name
- `rules` - List of grammar rules
- `tokens` - List of token kinds
- `keywords` - List of keywords
- `operators` - List of operators (for formatter metadata)

### Rule Definition

```gleam
/// Create a basic rule with alternatives
pub fn rule(name: String, alternatives: List(Alternative(a))) -> Rule(a)

/// Create a left-associative operator rule
pub fn left_assoc_rule(
  name: String,
  first_rule: String,
  operators: List(Operator(a)),
  precedence: Int,
) -> Rule(a)

/// Create a right-associative operator rule
pub fn right_assoc_rule(
  name: String,
  first_rule: String,
  operators: List(Operator(a)),
  precedence: Int,
) -> Rule(a)
```

### Alternative Definition

```gleam
/// Create an alternative with constructor
pub fn alt(
  pattern: Pattern(a),
  constructor: fn(List(Value(a))) -> a,
) -> Alternative(a)
```

### Pattern Helpers

```gleam
/// Match a token by kind
pub fn token_pattern(kind: String) -> Pattern(a)

/// Reference another rule
pub fn ref(rule: String) -> Pattern(a)

/// Sequence of patterns
pub fn seq(patterns: List(Pattern(a))) -> Pattern(a)

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

### Operator Helpers

```gleam
/// Create an operator with default layout
pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
) -> Operator(a)

/// Create an operator with custom layout
pub fn op_with_layout(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
  layout: OperatorLayout,
) -> Operator(a)

/// Default operator layout
pub fn default_op_layout(separator: String) -> OperatorLayout

/// Break before operator layout (like Haskell's $)
pub fn break_before_op_layout(separator: String) -> OperatorLayout

/// Compact operator layout (never break)
pub fn compact_op_layout(separator: String) -> OperatorLayout
```

### Metadata Extraction (for Formatters)

```gleam
/// Extract operator precedence table from grammar
pub fn extract_precedence_table(grammar: Grammar(a)) -> fn(String) -> Result(Int, Nil)

/// Extract operator layout table from grammar
pub fn extract_layout_table(grammar: Grammar(a)) -> fn(String) -> Result(OperatorLayout, Nil)

/// Get precedence for a constructor from grammar
pub fn get_precedence_for_constructor(
  grammar: Grammar(a),
  constructor_key: #(String, fn(a, a) -> a),
) -> Int

/// Get operator symbol for a constructor from grammar
pub fn get_operator_symbol_for_constructor(
  grammar: Grammar(a),
  constructor_key: #(String, fn(a, a) -> a),
) -> String

/// Format binary operator with precedence from grammar
pub fn format_binop_with_grammar(
  grammar: Grammar(a),
  format_fn: fn(a, Int, Grammar(a)) -> Doc,
  left: a,
  right: a,
  constructor_key: #(String, fn(a, a) -> a),
  parent_prec: Int,
) -> Doc
```

---

## Formatter Combinators

The formatter library provides 16+ combinators that reduce boilerplate:

### Binary Operators

```gleam
/// Format binary operator with automatic precedence handling
pub fn format_binop_auto(
  format_fn: fn(a, Int) -> Doc,
  left: a,
  right: a,
  separator: String,
  prec: Int,
  parent_prec: Int,
) -> Doc

/// Format binary operator with precedence from grammar
pub fn format_binop_with_grammar(
  grammar: Grammar(a),
  format_fn: fn(a, Int, Grammar(a)) -> Doc,
  left: a,
  right: a,
  constructor_key: #(String, fn(a, a) -> a),
  parent_prec: Int,
) -> Doc
```

### Unary Operators

```gleam
/// Format unary operator (prefix)
pub fn format_unary(op: String, operand: Doc) -> Doc

/// Format unary operator (postfix)
pub fn format_unary_postfix(operand: Doc, op: String) -> Doc
```

### Wrapped Expressions

```gleam
/// Format wrapped expression (parens, braces, brackets, etc.)
pub fn format_wrapped(open: String, content: Doc, close: String) -> Doc
```

### Lists

```gleam
/// Format list of items with separator
pub fn format_list(items: List(Doc), sep: Doc) -> Doc
```

### Function Application

```gleam
/// Format function application
pub fn format_application(fun: Doc, args: List(Doc)) -> Doc
```

### Lambda Abstraction

```gleam
/// Format lambda abstraction
pub fn format_lambda(params: List(String), body: Doc) -> Doc
```

### Records

```gleam
/// Format record with fields
pub fn format_record(fields: List(#(String, Doc))) -> Doc

/// Format record with automatic layout (inline or multi-line)
pub fn format_record_auto(fields: List(#(String, Doc)), width: Int) -> Doc
```

### Match Expressions

```gleam
/// Format match expression
pub fn format_match(scrutinee: Doc, cases: List(Doc)) -> Doc

/// Format single match case
pub fn format_case(pattern: Doc, guard: Option(Doc), body: Doc) -> Doc
```

### Layout Strategies

```gleam
/// Format inline (no breaks)
pub fn format_inline(format_fn: fn(a) -> Doc, value: a) -> Doc

/// Format with soft breaks (break if needed)
pub fn format_soft_break(format_fn: fn(a) -> Doc, value: a) -> Doc

/// Format with hard breaks (always break)
pub fn format_hard_break(format_fn: fn(a) -> Doc, value: a) -> Doc
```

---

## Common Rule Patterns

### Binary Operators (Left-Associative)

```gleam
// a + b + c = ((a + b) + c)
grammar.left_assoc_rule("Expr", "Term", [
  grammar.op("+", Add, 10),
  grammar.op("-", Sub, 10),
], 10)
```

### Binary Operators (Right-Associative)

```gleam
// a ^ b ^ c = (a ^ (b ^ c))
grammar.right_assoc_rule("Expr", "Factor", [
  grammar.op("^", Pow, 30),
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
)
```

---

## Migration Guide (v1 → v2)

### Builder Pattern → Direct Record

**Before (v1)**:
```gleam
use g <- grammar.define
g
|> grammar.name("MyLang")
|> grammar.start("Expr")
|> grammar.token("Number")
|> grammar.left_assoc("Expr", "Term", [...], 10)
```

**After (v2)**:
```gleam
grammar.Grammar(
  name: "MyLang",
  start: "Expr",
  tokens: ["Number"],
  operators: [...],
  rules: [
    grammar.left_assoc_rule("Expr", "Term", [...], 10),
  ],
)
```

### Removed Features

- **Builder pattern** - Replaced with direct record construction
- **Deconstructor** - Was a stub, never used
- **Formatter in grammar** - Formatters are now fully separate

### Simplified Features

- **OperatorLayout** - Now just `OperatorLayout(separator: String)` (removed unused fields)
- **op()** - Now just takes `keyword`, `constructor`, `precedence` (layout is optional)

---

## Best Practices

1. **Keep grammar declarative** - Define what to parse, not how
2. **Use precedence levels** - Higher number = tighter binding
3. **Provide constructors** - Each alternative needs a constructor function
4. **Test round-trips** - Verify parse → format → parse produces same AST
5. **Use formatter combinators** - 16+ combinators reduce boilerplate by 70-80%
6. **Extract metadata from grammar** - Use `extract_precedence_table()` for formatters
7. **Report errors with snippets** - Use `error_reporter` and `source_snippet` modules

---

## Examples

### Calculator Language

See `src/syntax/examples/calc.gleam` for a complete working example with:
- Addition, subtraction, multiplication, division
- Operator precedence (* and / bind tighter than + and -)
- Left-associative operators
- Parenthesized expressions
- Round-trip tested (parse → format → parse)
- Grammar-derived formatter with metadata-aware combinators

---

## Related Documents

- **[plans/syntax/01-overview.md](plans/syntax/01-overview.md)** - Grammar system overview
- **[plans/syntax/09-comprehensive-analysis.md](plans/syntax/09-comprehensive-analysis.md)** - Comprehensive analysis
- **[plans/syntax/10-refactoring-plan.md](plans/syntax/10-refactoring-plan.md)** - Refactoring plan
- **[docs/core.md](docs/core.md)** - Core language specification

---

## References

- [Grammar Implementation](src/syntax/grammar.gleam)
- [Lexer Implementation](src/syntax/lexer.gleam)
- [Formatter Implementation](src/syntax/formatter.gleam)
- [Source Snippet](src/syntax/source_snippet.gleam)
- [Error Reporter](src/syntax/error_reporter.gleam)
- [Calculator Example](src/syntax/examples/calc.gleam)
