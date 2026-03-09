# Parser Library

> **Goal**: Generic, composable parser combinators with Pratt parsing for expressions
> **Status**: ✅ Implemented
> **Date**: March 2025

---

## Overview

The parser library provides general-purpose parser combinators that work with any grammar. It uses:

1. **Token-based parsing** - Works with pre-tokenized input from lexer
2. **Pratt parsing** - Operator precedence parsing (1000+ lines)
3. **Error recovery** - Never panics, accumulates errors
4. **Source locations** - Track positions for error messages

---

## Core Types

```gleam
/// Parser that produces a value of type `a`
pub type Parser(a) {
  Parser(fn(State) -> Result(#(a, State), State))
}

/// Parser state
pub type State {
  State(
    tokens: List(Token),
    pos: Int,
    filename: String,
    expected: String,
  )
}

/// Parse result - always succeeds with AST and errors
pub type ParseResult(a) {
  ParseResult(
    ast: a,
    errors: List(ParseError),
  )
}

/// Parse error
pub type ParseError {
  ParseError(
    location: Location,
    message: String,
    expected: List(String),
    severity: ErrorSeverity,
  )
}

pub type ErrorSeverity {
  Error
  Warning
  Info
}
```

---

## Basic Combinators

### Core Functions

```gleam
/// Parser that succeeds with a value
pub fn ok(a: a) -> Parser(a)

/// Parser that always fails
pub fn fail() -> Parser(a)

/// Get current state
pub fn state() -> Parser(State)

/// Get current position
pub fn position() -> Parser(Position)
```

### Token Parsers

```gleam
/// Parse a specific token kind
pub fn token(kind: String) -> Parser(Token)

/// Parse a keyword (exact value match)
pub fn keyword(value: String) -> Parser(Token)

/// Parse an operator (exact value match)
pub fn op(value: String) -> Parser(Token)

/// Parse any token
pub fn any_token() -> Parser(Token)
```

### Sequence Combinators

```gleam
/// Chain parsers in sequence
pub fn chain(parsers: List(Parser(a))) -> Parser(List(a))

/// Parse zero or one
pub fn zero_or_one(parser: Parser(a)) -> Parser(Option(a))

/// Parse zero or more
pub fn zero_or_more(parser: Parser(a)) -> Parser(List(a))

/// Parse one or more
pub fn one_or_more(parser: Parser(a)) -> Parser(List(a))

/// Parse exactly n times
pub fn exactly(n: Int, parser: Parser(a)) -> Parser(List(a))
```

### Choice Combinators

```gleam
/// Try parsers in order, return first success
pub fn one_of(parsers: List(Parser(a))) -> Parser(a)

/// Commit to first successful parse
pub fn commit_one_of(parsers: List(Parser(a))) -> Parser(a)
```

### Padding and Delimiters

```gleam
/// Pad parser on the left
pub fn padded_l(padding: Parser(a), parser: Parser(b)) -> Parser(b)

/// Pad parser on the right
pub fn padded_r(padding: Parser(a), parser: Parser(b)) -> Parser(b)

/// Pad parser on both sides
pub fn padded(padding: Parser(a), parser: Parser(b)) -> Parser(b)

/// Parse between delimiters
pub fn inbetween(
  start: Parser(a),
  end: Parser(a),
  parser: Parser(b)
) -> Parser(b)

/// Parse separated by delimiter
pub fn separated_by(
  sep: Parser(a),
  parser: Parser(b)
) -> Parser(List(b))
```

### Lookahead and Assertions

```gleam
/// Lookahead without consuming
pub fn lookahead(parser: Parser(a)) -> Parser(a)

/// Negative lookahead
pub fn lookahead_not(parser: Parser(a)) -> Parser(Nil)

/// Assert a condition
pub fn assert(pred: fn(a) -> Bool, parser: Parser(a)) -> Parser(a)
```

---

## Expression Parsing (Pratt Parsing)

### Expression Parser Type

```gleam
/// Expression parser for Pratt parsing
pub type ExprParser(a) {
  Atom(fn(Parser(a)) -> Parser(a))
  Prefix(Int, fn(Parser(a)) -> Parser(a))
  InfixL(Int, fn(a, Parser(a)) -> Parser(a))
  InfixR(Int, fn(a, Parser(a)) -> Parser(a))
}
```

### Expression Combinators

```gleam
/// Atom parser
pub fn atom(
  f: fn(a) -> b,
  parser: Parser(a)
) -> ExprParser(b)

/// Group parser
pub fn group(
  open: Parser(a),
  close: Parser(a),
  spaces: Parser(b),
) -> ExprParser(c)

/// Prefix operator
pub fn prefix(
  precedence: Int,
  f: fn(Location, op, a) -> a,
  spaces: Parser(a),
  op: Parser(op)
) -> ExprParser(a)

/// Left-associative infix operator
pub fn infix_l(
  precedence: Int,
  f: fn(Location, op, a, a) -> a,
  spaces: Parser(a),
  op: Parser(op)
) -> ExprParser(a)

/// Right-associative infix operator
pub fn infix_r(
  precedence: Int,
  f: fn(Location, op, a, a) -> a,
  spaces: Parser(a),
  op: Parser(op)
) -> ExprParser(a)

/// Build expression parser with precedence
pub fn precedence(ops: List(ExprParser(a)), min_prec: Int) -> Parser(a)
```

### Usage Example

```gleam
import parser.{type Parser, atom, infix_l, prefix, precedence}

// Define operators
let ops = [
  // Atoms
  atom(fn(x) -> x, integer()),
  atom(fn(x) -> x, identifier()),

  // Prefix operators
  prefix(100, fn(loc, op, x) -> Neg(loc, x), spaces(), char("-")),

  // Infix operators (left-associative)
  infix_l(50, fn(loc, op, x, y) -> Add(loc, x, y), spaces(), char("+")),
  infix_l(50, fn(loc, op, x, y) -> Sub(loc, x, y), spaces(), char("-")),
  infix_l(60, fn(loc, op, x, y) -> Mul(loc, x, y), spaces(), char("*")),
  infix_l(60, fn(loc, op, x, y) -> Div(loc, x, y), spaces(), char("/")),

  // Right-associative operators
  infix_r(70, fn(loc, op, x, y) -> Pow(loc, x, y), spaces(), char("^")),
]

// Build expression parser
let expr = precedence(ops, 0)
```

---

## Error Handling and Recovery

### Error Recovery Strategies

```gleam
/// Sync to a synchronization point
pub fn sync_to(sync_points: List(Parser(a))) -> Parser(Nil)

/// Skip until end of line
pub fn sync_to_eol() -> Parser(Nil)

/// Skip current token
pub fn skip_token() -> Parser(Nil)

/// Insert a missing token
pub fn insert_token(token: a) -> Parser(a)
```

### Recovery Combinators

```gleam
/// Parse with recovery - always returns a result
pub fn recover(
  parser: Parser(a),
  recovery: Parser(a),
  error_msg: String
) -> Parser(ParseResult(a))

/// Parse with sync points
pub fn recover_with_sync(
  parser: Parser(a),
  sync_points: List(Parser(Nil)),
  error_msg: String
) -> Parser(ParseResult(a))

/// Convert parser to always succeed with errors
pub fn recover_all(parser: Parser(a), default: a) -> Parser(ParseResult(a))
```

### Error Reporting

```gleam
/// Format a single error
pub fn format_error(error: ParseError, source: String) -> String

/// Format multiple errors
pub fn format_errors(errors: List(ParseError), source: String) -> String

/// Format error with source snippet
pub fn format_error_with_snippet(
  error: ParseError,
  source: String,
  context_lines: Int
) -> String
```

### Example Error Output

```
error: Expected expression
  ┌─ main.gleam:5:10
  │
5 │ let x = + y;
  │          ^ Expected expression after operator

  Hint: Try adding a value after the operator

warning: Missing semicolon
  ┌─ main.gleam:10:15
   │
10 │ let y = 42
   │               ^ Expected ';'

   Hint: Add ';' at the end of the statement

Found 2 errors, 1 warning
```

---

## Grammar-to-Parser Generation

### Main Parse Function

```gleam
pub fn parse(g: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(source)

  case dict.get(g.rules, g.start) {
    Ok(rule) -> {
      case parse_rule(g, rule, tokens, 0) {
        Ok(#(ast, _)) -> ParseResult(ast: ast, errors: [])
        Error(_) -> ParseResult(ast: panic, errors: [])
      }
    }
    Error(_) -> ParseResult(ast: panic, errors: [])
  }
}
```

### Rule Parsing

```gleam
fn parse_rule(
  g: Grammar(a),
  rule: Rule(a),
  tokens: List(Token),
  pos: Int,
) -> Result(#(a, Int), ParseError) {
  case rule.alternatives {
    [] -> Error(...)
    [alt, ..rest] -> {
      case try_alternative(g, alt, tokens, pos) {
        Ok(result) -> Ok(result)
        Error(_) -> parse_rule(g, Rule(..rule, alternatives: rest), tokens, pos)
      }
    }
  }
}
```

### Pattern Parsing

```gleam
fn parse_pattern(
  g: Grammar(a),
  pattern: Pattern,
  tokens: List(Token),
  pos: Int,
) -> Result(#(Value(a), Int), ParseError) {
  case pattern {
    TokenKind(kind) -> parse_token_kind(tokens, pos, kind)
    Keyword(value) -> parse_keyword_value(tokens, pos, value)
    Ref(name) -> parse_ref(g, name, tokens, pos)
    Seq(patterns) -> parse_seq(g, patterns, tokens, pos, [])
    Choice(alts) -> parse_choice(g, alts, tokens, pos)
    Opt(p) -> parse_opt(g, p, tokens, pos)
    Many(p) -> parse_many(g, p, tokens, pos, [])
    Sep1(item, sep) -> parse_sep1(g, item, sep, tokens, pos, [])
    Parens(rule) -> parse_parens(g, rule, tokens, pos)
  }
}
```

### Left-Associative Parsing

```gleam
/// Parse left-associative operator sequence
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
```

---

## Implementation Notes

### Key Design Decisions

1. **Token-Based**: Parser works with pre-tokenized input (not raw strings)
2. **State-Passing**: Explicit state threading for position tracking
3. **Error Accumulation**: Never stop on first error
4. **Left-Assoc Special Handling**: Dedicated parsing logic for operator sequences

### Performance Considerations

1. **No Backtracking**: Once committed, don't backtrack (use `commit`)
2. **Left-Factoring**: Grammar should be left-factored for efficiency
3. **Token Caching**: Cache token lookups by position

### Limitations

1. **Recursive Grammars**: Limited support for left-recursive rules
2. **Error Quality**: Generic errors, not rule-specific messages
3. **Recovery**: Basic sync-point recovery, not phrase-level

---

## Testing

### Test Patterns

```gleam
// Number parsing
assert_parse("42", Int(42))
assert_parse("123", Int(123))

// Operator precedence
assert_parse("1 + 2 * 3", Add(Int(1), Mul(Int(2), Int(3))))
assert_parse("(1 + 2) * 3", Mul(Add(Int(1), Int(2)), Int(3)))

// Left associativity
assert_parse("1 + 2 + 3", Add(Add(Int(1), Int(2)), Int(3)))
assert_parse("12 / 3 * 2", Mul(Div(Int(12), Int(3)), Int(2)))

// Error cases
assert_error("abc", "Expected expression")
assert_error("1 +", "Expected expression after operator")
```

---

## See Also

- [Grammar DSL](./02-grammar-dsl.md)
- [Formatter Library](./04-formatter-library.md)
- [Lexer](../../src/lexer.gleam)
