# Generic Grammar System - Implementation Plan (Revised)

## Problem

The current implementation has:
- `src/grammar.gleam` - Generic grammar types (but incomplete)
- `src/calc/grammar.gleam` - Custom parser that doesn't use generic grammar
- `src/calc/format.gleam` - Separate formatter

This defeats the purpose. We need:
- `src/calc/syntax.gleam` - Only grammar definition
- Parser and formatter generated from grammar

## Key Insight

**Formatting is inherently AST-specific** - you need to pattern-match on concrete types.
The grammar can provide *structure* and *precedence*, but formatting logic is AST-specific.

## Solution Overview

The grammar defines:
1. **Structure** - What to parse (Symbol tree)
2. **Construction** - How to build AST from parsed children
3. **Precedence** - Binding strength for parenthesization

The formatter:
1. Pattern-matches on concrete AST (AST-specific)
2. Uses grammar precedence for parenthesization (generic helper)

## Data Structures

### Grammar Type

```gleam
pub type Grammar(ast) {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule(ast)),
    tokens: List(String),
    keywords: List(String),
  )
}
```

### Rule Type

```gleam
pub type Rule(ast) {
  Rule(
    name: String,
    definition: Symbol,
    constructor: fn(List(ParseChild)) -> ast,
    precedence: Int,
  )
}

pub type ParseChild {
  ChildToken(Token)
  ChildAST(any)  // Type erased - will be the AST type
}
```

### Symbol Type

```gleam
pub type Symbol {
  Token(kind: String)
  Keyword(value: String)
  Ref(rule: String)
  Seq(symbols: List(Symbol))
  Choice(alts: List(Symbol))
  Opt(symbol: Symbol)
  Many(symbol: Symbol)
  Sep(item: Symbol, sep: Symbol)
  Sep1(item: Symbol, sep: Symbol)
}
```

## Parser Implementation (Generic)

```gleam
pub fn parse(g: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(source)
  let tree = parse_symbol(g, g.start, tokens, 0)
  case tree {
    Ok(result) -> {
      let ast = apply_constructor(g, g.start, result.children)
      ParseResult(ast: ast, errors: [])
    }
    Error(errors) -> ParseResult(ast: panic, errors: errors)
  }
}
```

## Formatter Implementation (Hybrid)

### Generic Helper for Precedence

```gleam
// In src/grammar.gleam
pub fn format_with_precedence(
  g: Grammar(a),
  ast: a,
  parent_prec: Int,
  format_fn: fn(a) -> String,
) -> String {
  let prec = get_precedence(g, ast)
  let s = format_fn(ast)
  case prec < parent_prec {
    True -> "(" <> s <> ")"
    False -> s
  }
}
```

### AST-Specific Formatter

```gleam
// In src/calc/syntax.gleam
pub fn format(expr: Expr) -> String {
  format_expr(expr, 0)
}

fn format_expr(expr: Expr, parent_prec: Int) -> String {
  grammar.format_with_precedence(calc_grammar(), expr, parent_prec, fn(e) {
    case e {
      Int(n) -> int.to_string(n)
      Add(l, r) -> format_binop(l, r, " + ", 10)
      Mul(l, r) -> format_binop(l, r, " * ", 20)
    }
  })
}
```

## Implementation Steps

### Step 1: Define Core Types in `src/grammar.gleam`

- `Grammar(ast)`, `Rule(ast)`, `Symbol`, `ParseChild`
- Parser functions: `parse()`, `parse_symbol()`, `apply_constructor()`
- Formatter helper: `format_with_precedence()`

### Step 2: Define Calculator Grammar in `src/calc/syntax.gleam`

```gleam
import grammar
import calc/ast

pub fn calc_grammar() -> Grammar(Expr) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.rule("Expr",
      grammar.seq([grammar.ref("Term"), grammar.opt(greater_than_10(grammar.seq([grammar.token("Operator"), grammar.ref("Expr")])))]),
      fn(children) { build_add(children) },
      10,
  )
  // ... more rules
}

pub fn parse(source: String) -> ParseResult(Expr) {
  grammar.parse(calc_grammar(), source)
}

pub fn format(ast: Expr) -> String {
  format_expr(ast, 0)
}
```

### Step 3: Remove Old Files

- Delete `src/calc/grammar.gleam` (custom parser)
- Delete `src/calc/format.gleam` (separate formatter)

### Step 4: Update Tests

- Import from `calc/syntax` instead of separate modules
