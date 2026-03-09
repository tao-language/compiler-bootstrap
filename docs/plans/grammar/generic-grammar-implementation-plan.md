# Generic Grammar System - Complete Implementation Plan

## Overview

A generic grammar DSL that generates both parsers and formatters for any AST type. The grammar is the **single source of truth** - it defines structure, precedences, operators, and formatting templates.

---

## Data Structures

### Core Types

```gleam
import gleam/dict.{type Dict}
import lexer.{type Token}
import parser.{type ParseResult}

/// Associativity of operators
pub type Associativity {
  Left
  Right
  None
}

/// Generic grammar parameterized by AST type
pub type Grammar(ast) {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule(ast)),
    tokens: List(String),
    keywords: List(String),
  )
}

/// Grammar rule with full parsing and formatting info
pub type Rule(ast) {
  Rule(
    name: String,
    definition: Symbol,
    constructor: fn(List(ParseChild(ast))) -> ast,
    precedence: Int,
    associativity: Associativity,
    format_template: FormatTemplate,
  )
}

/// Format template - how to format children
pub type FormatTemplate {
  /// Simple sequence: format children with separators
  TemplateSeq(separators: List(String))
  /// Custom formatter for complex cases
  TemplateCustom
}

/// Child of a parse result
pub type ParseChild(ast) {
  ChildToken(Token)
  ChildAST(ast)
}

/// Grammar symbol (not generic - describes structure)
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
  /// Left-associative operator sequence (special handling)
  LeftAssoc(first: Symbol, ops: List(Operator))
}

/// Operator for left_assoc
pub type Operator {
  Operator(
    keyword: String,
    constructor: fn(ast, ast) -> ast,
    format_separator: String,
  )
}

/// Internal parse result
type InternalResult(ast) {
  InternalResult(children: List(ParseChild(ast)), pos: Int)
}
```

---

## Grammar Construction API

### Basic Functions

```gleam
/// Create new empty grammar
pub fn new() -> Grammar(a) {
  Grammar(
    name: "Grammar",
    start: "Start",
    rules: dict.new(),
    tokens: [],
    keywords: [],
  )
}

/// Set start rule
pub fn start(g: Grammar(a), rule: String) -> Grammar(a) {
  Grammar(..g, start: rule)
}

/// Add token kind
pub fn with_token(g: Grammar(a), kind: String) -> Grammar(a) {
  Grammar(..g, tokens: [kind, ..g.tokens])
}

/// Add keyword
pub fn with_keyword(g: Grammar(a), kw: String) -> Grammar(a) {
  Grammar(..g, keywords: [kw, ..g.keywords])
}
```

### Rule Definition

```gleam
/// Add basic rule
pub fn rule(
  g: Grammar(a),
  name: String,
  definition: Symbol,
  constructor: fn(List(ParseChild(a))) -> a,
  precedence: Int,
  format_template: FormatTemplate,
) -> Grammar(a) {
  let rule = Rule(
    name: name,
    definition: definition,
    constructor: constructor,
    precedence: precedence,
    associativity: None,
    format_template: format_template,
  )
  let rules = dict.insert(g.rules, name, rule)
  Grammar(..g, rules: rules)
}

/// Add left-associative operator rule (convenience function)
pub fn left_assoc(
  g: Grammar(a),
  name: String,
  first: Symbol,
  ops: List(Operator),
  precedence: Int,
) -> Grammar(a) {
  // Build format template from operators
  let separators = list.map(ops, fn(op) { op.format_separator })
  
  // Build constructor that folds left-to-right
  let constructor = make_left_assoc_constructor(ops)
  
  // Build symbol for LeftAssoc
  let definition = LeftAssoc(first, ops)
  
  rule(g, name, definition, constructor, precedence, TemplateSeq(separators))
}

/// Create operator definition
pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  format_separator: String,
) -> Operator {
  Operator(keyword, constructor, format_separator)
}
```

### Symbol Constructors

```gleam
pub fn token(kind: String) -> Symbol { Token(kind) }
pub fn keyword(value: String) -> Symbol { Keyword(value) }
pub fn ref(name: String) -> Symbol { Ref(name) }
pub fn seq(symbols: List(Symbol)) -> Symbol { Seq(symbols) }
pub fn choice(alts: List(Symbol)) -> Symbol { Choice(alts) }
pub fn opt(symbol: Symbol) -> Symbol { Opt(symbol) }
pub fn many(symbol: Symbol) -> Symbol { Many(symbol) }
pub fn sep(item: Symbol, sep: Symbol) -> Symbol { Sep(item, sep) }
pub fn sep1(item: Symbol, sep: Symbol) -> Symbol { Sep1(item, sep) }
```

---

## Parser Implementation

### Main Parse Function

```gleam
/// Parse source using grammar
pub fn parse(g: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(lexer.default_config(), g.name, source)
  
  case dict.get(g.rules, g.start) {
    Ok(rule) -> {
      case parse_symbol(g, rule.definition, tokens, 0) {
        Ok(result) -> {
          let ast = rule.constructor(result.children)
          ParseResult(ast: ast, errors: [])
        }
        Error(_) -> ParseResult(ast: panic as "Parse failed", errors: [])
      }
    }
    Error(_) -> ParseResult(ast: panic as "No start rule", errors: [])
  }
}
```

### Symbol Parsing

```gleam
fn parse_symbol(
  g: Grammar(a),
  symbol: Symbol,
  tokens: List(Token),
  pos: Int,
) -> Result(InternalResult(a), Nil) {
  case symbol {
    Token(kind) -> parse_token_kind(tokens, pos, kind)
    Keyword(value) -> parse_keyword_value(tokens, pos, value)
    Ref(name) -> parse_ref(g, name, tokens, pos)
    Seq(symbols) -> parse_seq(g, symbols, tokens, pos, [])
    Choice(alts) -> parse_choice(g, alts, tokens, pos)
    Opt(sym) -> parse_opt(g, sym, tokens, pos)
    Many(sym) -> parse_many(g, sym, tokens, pos, [])
    Sep(item, sep) -> parse_sep(g, item, sep, tokens, pos, [])
    Sep1(item, sep) -> parse_sep1(g, item, sep, tokens, pos, [])
    LeftAssoc(first, ops) -> parse_left_assoc(g, first, ops, tokens, pos)
  }
}
```

### Left-Associative Parsing (Critical!)

```gleam
/// Parse left-associative operator sequence
/// This is the key function that fixes the associativity bug!
fn parse_left_assoc(
  g: Grammar(a),
  first: Symbol,
  ops: List(Operator),
  tokens: List(Token),
  pos: Int,
) -> Result(InternalResult(a), Nil) {
  // Parse the first element
  case parse_symbol(g, first, tokens, pos) {
    Ok(result) -> {
      // Get the first AST value
      let first_ast = case result.children {
        [ChildAST(ast)] -> ast
        _ -> Error(Nil)
      }
      
      // Parse operators and fold left-to-right
      parse_left_assoc_loop(first_ast, g, ops, tokens, result.pos, [])
    }
    Error(_) -> Error(Nil)
  }
}

fn parse_left_assoc_loop(
  left: a,
  g: Grammar(a),
  ops: List(Operator),
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  // Try to parse an operator
  case parse_operator(ops, tokens, pos) {
    Ok(#(op, new_pos)) -> {
      // Parse the next element
      case parse_symbol(g, Ref("Term"), tokens, new_pos) {
        // Note: "Term" is a placeholder - in real impl, need to pass the right ref
        Ok(result) -> {
          case result.children {
            [ChildAST(right)] -> {
              // Apply the operator constructor (left-associative!)
              let new_left = op.constructor(left, right)
              // Continue loop with new left value
              parse_left_assoc_loop(new_left, g, ops, tokens, result.pos, children)
            }
            _ -> Ok(InternalResult(children: [ChildAST(left)], pos: pos))
          }
        }
        Error(_) -> Ok(InternalResult(children: [ChildAST(left)], pos: pos))
      }
    }
    Error(_) -> {
      // No more operators, return accumulated result
      Ok(InternalResult(children: [ChildAST(left)], pos: pos))
    }
  }
}

fn parse_operator(
  ops: List(Operator),
  tokens: List(Token),
  pos: Int,
) -> Result(#(Operator, Int), Nil) {
  case get_token(tokens, pos) {
    Ok(token) -> {
      case list.find(ops, fn(op) { op.keyword == token.value }) {
        Ok(op) -> Ok(#(op, pos + 1))
        Error(_) -> Error(Nil)
      }
    }
    Error(_) -> Error(Nil)
  }
}
```

### Basic Parsing Functions

```gleam
fn parse_token_kind(tokens: List(Token), pos: Int, kind: String) -> Result(InternalResult(a), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.kind == kind -> {
      Ok(InternalResult(children: [ChildToken(token)], pos: pos + 1))
    }
    _ -> Error(Nil)
  }
}

fn parse_keyword_value(tokens: List(Token), pos: Int, value: String) -> Result(InternalResult(a), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.kind == "Operator" && token.value == value -> {
      Ok(InternalResult(children: [ChildToken(token)], pos: pos + 1))
    }
    _ -> Error(Nil)
  }
}

fn parse_ref(g: Grammar(a), name: String, tokens: List(Token), pos: Int) -> Result(InternalResult(a), Nil) {
  case dict.get(g.rules, name) {
    Ok(rule) -> {
      case parse_symbol(g, rule.definition, tokens, pos) {
        Ok(result) -> {
          // Apply constructor to get actual AST
          let ast = rule.constructor(result.children)
          Ok(InternalResult(children: [ChildAST(ast)], pos: result.pos))
        }
        Error(_) -> Error(Nil)
      }
    }
    Error(_) -> Error(Nil)
  }
}

fn parse_seq(
  g: Grammar(a),
  symbols: List(Symbol),
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case symbols {
    [] -> Ok(InternalResult(children: children, pos: pos))
    [sym, ..rest] -> {
      case parse_symbol(g, sym, tokens, pos) {
        Ok(result) -> parse_seq(g, rest, tokens, result.pos, list.append(children, result.children))
        Error(_) -> Error(Nil)
      }
    }
  }
}

fn parse_choice(
  g: Grammar(a),
  alts: List(Symbol),
  tokens: List(Token),
  pos: Int,
) -> Result(InternalResult(a), Nil) {
  case alts {
    [] -> Error(Nil)
    [alt, ..rest] -> {
      case parse_symbol(g, alt, tokens, pos) {
        Ok(result) -> Ok(result)
        Error(_) -> parse_choice(g, rest, tokens, pos)
      }
    }
  }
}

fn parse_opt(
  g: Grammar(a),
  sym: Symbol,
  tokens: List(Token),
  pos: Int,
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, sym, tokens, pos) {
    Ok(result) -> Ok(result)
    Error(_) -> Ok(InternalResult(children: [], pos: pos))
  }
}

fn parse_many(
  g: Grammar(a),
  sym: Symbol,
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, sym, tokens, pos) {
    Ok(result) -> parse_many(g, sym, tokens, result.pos, list.append(children, result.children))
    Error(_) -> Ok(InternalResult(children: children, pos: pos))
  }
}

fn parse_sep(
  g: Grammar(a),
  item: Symbol,
  sep: Symbol,
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, item, tokens, pos) {
    Ok(result) -> parse_sep_loop(g, item, sep, tokens, result.pos, list.append(children, result.children))
    Error(_) -> Ok(InternalResult(children: children, pos: pos))
  }
}

fn parse_sep_loop(
  g: Grammar(a),
  item: Symbol,
  sep: Symbol,
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, sep, tokens, pos) {
    Ok(_) -> {
      case parse_symbol(g, item, tokens, pos) {
        Ok(result) -> parse_sep_loop(g, item, sep, tokens, result.pos, list.append(children, result.children))
        Error(_) -> Ok(InternalResult(children: children, pos: pos))
      }
    }
    Error(_) -> Ok(InternalResult(children: children, pos: pos))
  }
}

fn parse_sep1(
  g: Grammar(a),
  item: Symbol,
  sep: Symbol,
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, item, tokens, pos) {
    Ok(result) -> parse_sep_loop(g, item, sep, tokens, result.pos, list.append(children, result.children))
    Error(_) -> Error(Nil)
  }
}

fn get_token(tokens: List(Token), pos: Int) -> Result(Token, Nil) {
  get_token_loop(tokens, pos, 0)
}

fn get_token_loop(tokens: List(Token), pos: Int, current: Int) -> Result(Token, Nil) {
  case tokens {
    [] -> Error(Nil)
    [token, ..rest] -> {
      case current == pos {
        True -> Ok(token)
        False -> get_token_loop(rest, pos, current + 1)
      }
    }
  }
}
```

---

## Formatter Implementation

### Main Format Function

```gleam
/// Format AST using grammar
pub fn format(g: Grammar(a), ast: a) -> String {
  // Create recursive formatter that can call itself
  let rec format_self = fn(child_ast) {
    format_with_grammar(g, g.start, child_ast, format_self, 0)
  }
  format_self(ast)
}

fn format_with_grammar(
  g: Grammar(a),
  rule_name: String,
  ast: a,
  format_self: fn(a) -> String,
  parent_prec: Int,
) -> String {
  case dict.get(g.rules, rule_name) {
    Ok(rule) -> {
      let prec = rule.precedence
      let doc = format_by_template(rule.format_template, ast, format_self)
      
      // Add parens if child precedence < parent precedence
      case prec < parent_prec {
        True -> "(" <> doc <> ")"
        False -> doc
      }
    }
    Error(_) -> "<unknown>"
  }
}

fn format_by_template(
  template: FormatTemplate,
  ast: a,
  format_self: fn(a) -> String,
) -> String {
  case template {
    TemplateSeq(separators) -> {
      // For simple sequences, use default formatting
      // In real impl, would need to extract children from ast
      format_default(ast, format_self, separators)
    }
    TemplateCustom -> {
      // Custom formatting handled by grammar-specific code
      "<custom>"
    }
  }
}

fn format_default(
  ast: a,
  format_self: fn(a) -> String,
  separators: List(String),
) -> String {
  // Default implementation - just format the ast
  // Real impl would pattern-match on ast type
  format_self(ast)
}
```

---

## Helper Functions

### Left-Associative Constructor Generator

```gleam
/// Generate constructor for left-associative operators
fn make_left_assoc_constructor(ops: List(Operator)) -> fn(List(ParseChild(a))) -> a {
  fn(children) {
    case children {
      [ChildAST(first), ChildAST(ops_list)] -> {
        fold_ops(first, ops_list, ops)
      }
      [ChildAST(first)] -> first
      _ -> panic as "Invalid left_assoc children"
    }
  }
}

fn fold_ops(
  left: a,
  ops: List(ParseChild(a)),
  operators: List(Operator),
) -> a {
  case ops {
    [] -> left
    [ChildToken(token), ChildAST(right), ..rest] -> {
      case list.find(operators, fn(op) { op.keyword == token.value }) {
        Ok(op) -> {
          let new_left = op.constructor(left, right)
          fold_ops(new_left, rest, operators)
        }
        Error(_) -> left
      }
    }
    _ -> left
  }
}
```

---

## Example Usage: Calculator Language

```gleam
import calc/ast.{type Expr, Add, Int, Mul}
import grammar

pub fn calc_grammar() -> grammar.Grammar(Expr) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.with_token("Number")
  |> grammar.with_token("Operator")
  |> grammar.with_token("LParen")
  |> grammar.with_token("RParen")
  
  // expr -> term (('+' | '-') term)*
  |> grammar.left_assoc(
    "Expr",
    grammar.ref("Term"),
    [
      grammar.op("+", fn(l, r) { Add(l, r) }, " + "),
      grammar.op("-", fn(l, r) { panic as "TODO" }, " - "),
    ],
    10,
  )
  
  // term -> factor (('*' | '/') factor)*
  |> grammar.left_assoc(
    "Term",
    grammar.ref("Factor"),
    [
      grammar.op("*", fn(l, r) { Mul(l, r) }, " * "),
      grammar.op("/", fn(l, r) { panic as "TODO" }, " / "),
    ],
    20,
  )
  
  // factor -> NUMBER | '(' expr ')'
  |> grammar.rule(
    "Factor",
    grammar.choice([
      grammar.token("Number"),
      grammar.seq([
        grammar.token("LParen"),
        grammar.ref("Expr"),
        grammar.token("RParen"),
      ]),
    ]),
    fn(children) {
      case children {
        [ChildToken(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
        [_, ChildAST(expr), _] -> expr
        _ -> panic as "Invalid factor"
      }
    },
    30,
    grammar.TemplateSeq([]),
  )
}

pub fn parse(source: String) -> parser.ParseResult(Expr) {
  grammar.parse(calc_grammar(), source)
}

pub fn format(ast: Expr) -> String {
  grammar.format(calc_grammar(), ast)
}
```

---

## Implementation Order

1. **Define Types** - `Grammar`, `Rule`, `Symbol`, `ParseChild`, `FormatTemplate`, `Operator`
2. **Implement Basic Grammar Construction** - `new()`, `start()`, `with_token()`, `with_keyword()`, `rule()`
3. **Implement Symbol Constructors** - `token()`, `keyword()`, `ref()`, `seq()`, `choice()`, etc.
4. **Implement Basic Parser** - `parse()`, `parse_symbol()`, `parse_seq()`, `parse_choice()`, etc.
5. **Implement Left-Associative Parsing** - `parse_left_assoc()`, `parse_left_assoc_loop()`, `parse_operator()`
6. **Implement Formatter** - `format()`, `format_with_grammar()`, `format_by_template()`
7. **Implement Helper Functions** - `left_assoc()`, `op()`, `make_left_assoc_constructor()`, `fold_ops()`
8. **Test with Calculator Example** - Verify parsing, formatting, round-trips

---

## Key Design Decisions

1. **Left-Associativity**: Special `LeftAssoc` symbol type with dedicated parsing logic
2. **Recursive Formatter**: Formatter takes itself as argument for recursive calls
3. **Format Templates**: Grammar provides separators, formatter uses them
4. **Operator Definitions**: Grammar knows keywords, constructors, and format strings
5. **Precedence Handling**: Each rule has precedence, formatter adds parens as needed

---

## Testing Checklist

- [ ] `1 + 2` parses as `Add(Int(1), Int(2))`
- [ ] `1 + 2 + 3` parses as `Add(Add(Int(1), Int(2)), Int(3))` (left-associative)
- [ ] `2 * 3 * 4` parses as `Mul(Mul(Int(2), Int(3)), Int(4))` (left-associative)
- [ ] `1 + 2 * 3` parses as `Add(Int(1), Mul(Int(2), Int(3)))` (precedence)
- [ ] `(1 + 2) * 3` parses as `Mul(Add(Int(1), Int(2)), Int(3))` (parens)
- [ ] `format(parse("1 + 2 * 3"))` returns `"1 + 2 * 3"` (no extra parens)
- [ ] `format(parse("(1 + 2) * 3"))` returns `"(1 + 2) * 3"` (preserves parens)
