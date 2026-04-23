// ============================================================================
// GRAMMAR - Unified Grammar DSL
// ============================================================================
import gleam/dict.{type Dict}
import gleam/list
import gleam/result
import gleam/string
import syntax/formatter.{type Doc, concat, parens, text}
import syntax/lexer.{type Token}

// ============================================================================
// TYPES
// ============================================================================

/// Source location span
pub type Span {
  Span(
    file: String,
    start_line: Int,
    // 1-based
    start_col: Int,
    // 1-based
    end_line: Int,
    // 1-based
    end_col: Int,
    // 1-based
  )
}

pub type Associativity {
  Left
  Right
  NonAssoc
}

/// Operator kind - determines parsing direction and formatting
///
/// Only 4 kinds: Prefix, Postfix, InfixLeft, InfixRight
/// Complex operators (ternary, slice, index) are Infix with structured postfix.
pub type OperatorKind {
  KindPrefix
  KindPostfix
  InfixLeft
  InfixRight
}

/// Describes what comes AFTER the rhs expression in an infix operator
///
/// This is recursive to handle ternary, slice, etc.
///
/// Examples:
/// - `x + y` → None (nothing after rhs)
/// - `a[i]` → Close("]") (just closing token)
/// - `a ? b : c` → Continue(":", None) (separator + nothing more)
/// - `a[b:c]` → Continue(":", Close("]")) (separator + closing)
pub type PostfixPattern {
  None
  Close(token: String)
  Continue(separator: String, rest: PostfixPattern)
}

/// Global formatter configuration
pub type FormatterConfig {
  FormatterConfig(width: Int, indent_string: String, indent_level: Int)
}

/// Layout hint for sequence items
pub type LayoutHint {
  SoftBreak
  // Space when flat, newline+indent when broken
  HardBreak
  // Always newline+indent
  Space
  // Always space
  NoSeparator
  // No separator
}

/// Sequence item with layout hint
pub type SeqItem(a) {
  SeqItem(pattern: Pattern(a), layout_hint: LayoutHint)
}

/// Layout configuration for operators (deprecated - use PostfixPattern)
pub type OperatorLayout {
  OperatorLayout(separator: String)
}

pub type LayoutStyle {
  Inline
  BreakAfterOperator(indent: Int)
  BreakBeforeOperator(indent: Int)
  Block(open: String, close: String, indent: Int)
}

pub type Pattern(a) {
  TokenKind(kind: String)
  Keyword(value: String)
  Op(value: String)
  Ref(rule: String)
  Seq(patterns: List(Pattern(a)))
  SeqWithLayout(items: List(SeqItem(a)))
  Choice(alts: List(Pattern(a)))
  Opt(pattern: Pattern(a))
  Many(pattern: Pattern(a))
  Sep1(item: Pattern(a), sep: Pattern(a))
  Parens(rule: String)
  /// Delimited list: open item (sep item)* close
  /// Supports empty lists, single items, and multiple items
  /// Examples: (), (x), (x, y, z), [x, y], {x: a, y: b}
  Delimited(open: Pattern(a), item: Pattern(a), sep: Pattern(a), close: Pattern(a))
}

pub type Alternative(a) {
  Alternative(pattern: Pattern(a), constructor: fn(List(Value(a))) -> a)
}

pub type Rule(a) {
  Rule(name: String, alternatives: List(Alternative(a)), precedence: Int)
}

/// Complete operator metadata
///
/// Contains everything needed to parse and format the operator.
/// No language-specific assumptions.
pub type Operator(a) {
  /// Prefix operator: <symbol> <expr>
  Prefix(precedence: Int, symbol: String, constructor: fn(a) -> a)

  /// Postfix operator: <expr> <symbol>
  Postfix(precedence: Int, symbol: String, constructor: fn(a) -> a)

  /// Infix operator: lhs <infix_op> rhs <postfix>
  /// Examples:
  /// - x + y: infix_op="+", postfix=None
  /// - a[i]: infix_op="[", postfix=Close("]")
  /// - a ? b : c: infix_op="?", postfix=Continue(":", None)
  Infix(
    kind: OperatorKind,
    precedence: Int,
    infix_op: String,
    postfix: PostfixPattern,
    constructor: fn(a, a) -> a,
  )
}

pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: List(Rule(a)),
    tokens: List(String),
    keywords: List(String),
    operators: List(#(String, Operator(a))),
    // Keyed by primary symbol for lookup
  )
}

pub type Value(a) {
  TokenValue(Token)
  KeywordValue(Token)
  AstValue(a)
  ParensValue(List(Value(a)))
  ListValue(List(Value(a)))
}

pub type ParseError {
  ParseError(span: Span, expected: String, got: String, context: String)
}

pub type ParseResult(a) {
  ParseResult(ast: a, errors: List(ParseError))
}

// ============================================================================
// GRAMMAR DEFINITION API
// ============================================================================

/// Create a left-associative operator rule
pub fn left_assoc_rule(
  name: String,
  first_rule: String,
  operators: List(#(String, Operator(a))),
  precedence: Int,
) -> Rule(a) {
  let op_alt = create_operator_pattern(operators, first_rule)
  Rule(name: name, alternatives: [op_alt], precedence: precedence)
}

/// Create a right-associative operator rule
pub fn right_assoc_rule(
  name: String,
  first_rule: String,
  operators: List(#(String, Operator(a))),
  precedence: Int,
) -> Rule(a) {
  let op_alts =
    list.map(operators, fn(item) {
      let #(symbol, op) = item
      let pattern = Seq([Ref(first_rule), Keyword(symbol), Ref(name)])
      Alternative(pattern: pattern, constructor: fn(values) {
        case values {
          [AstValue(left), KeywordValue(_), AstValue(right)] ->
            case op {
              Infix(_, _, _, _, constructor) -> constructor(left, right)
              _ -> panic as "right_assoc: expected Infix operator"
            }
          _ -> panic as "right_assoc: expected 3 values"
        }
      })
    })
  let first_alt =
    alt(ref(first_rule), fn(values) {
      case values {
        [AstValue(first)] -> first
        _ -> panic as "right_assoc: expected single value"
      }
    })
  Rule(name: name, alternatives: [first_alt, ..op_alts], precedence: precedence)
}

/// Create a rule with alternatives
pub fn rule(name: String, alternatives: List(Alternative(a))) -> Rule(a) {
  Rule(name: name, alternatives: alternatives, precedence: 0)
}

// ============================================================================
// PARSER
// ============================================================================

/// Check if a string is a single lowercase letter (a-z).
/// Used to distinguish word-based infix operators ("and", "or")
/// from symbol-based ones ("+", "&&", etc.).
fn is_word_symbol(s: String) -> Bool {
  case string.pop_grapheme(s) {
    Ok(#(first, _rest)) -> is_lowercase_letter(first)
    Error(_) -> False
  }
}

fn is_lowercase_letter(c: String) -> Bool {
  let codepoints = string.to_utf_codepoints(c)
  case codepoints {
    [cp] -> {
      let code = string.utf_codepoint_to_int(cp)
      code >= 97 && code <= 122  // 'a' to 'z'
    }
    _ -> False
  }
}

fn create_operator_pattern(
  operators: List(#(String, Operator(a))),
  first_rule: String,
) -> Alternative(a) {
  let op_choice =
    Choice(
      list.map(operators, fn(item) {
        let #(symbol, _op) = item
        // Word-based operators (like "and", "or") use Keyword pattern
        // Symbol-based operators (like "+", "&&") use Op pattern
        let pattern = case is_word_symbol(symbol) {
          True -> Keyword(symbol)   // Word-based: "and", "or"
          False -> Op(symbol)       // Symbol-based: "+", "&&", etc.
        }
        Seq([pattern, Ref(first_rule)])
      }),
    )
  let pattern =
    Seq([
      Ref(first_rule),
      Many(op_choice),
    ])
  Alternative(pattern: pattern, constructor: fn(values) {
    case values {
      [AstValue(first), ..rest] -> {
        fold_operators_multi(first, rest, operators)
      }
      _ -> panic as "left_assoc constructor: unexpected values"
    }
  })
}

fn fold_operators_multi(
  first: a,
  rest_values: List(Value(a)),
  operators: List(#(String, Operator(a))),
) -> a {
  case rest_values {
    [] -> first
    [op_right, ..more] -> {
      case op_right {
        ListValue([TokenValue(op_token), AstValue(right)]) -> {
          apply_operator(first, op_token.value, right, more, operators)
        }
        ListValue([KeywordValue(op_token), AstValue(right)]) -> {
          // Word-based operators (e.g., "and", "or") produce KeywordValue
          apply_operator(first, op_token.value, right, more, operators)
        }
        _ -> first
      }
    }
  }
}

fn apply_operator(
  first: a,
  op_symbol: String,
  right: a,
  more: List(Value(a)),
  operators: List(#(String, Operator(a))),
) -> a {
  let found =
    list.find(operators, fn(item) {
      let #(sym, _) = item
      sym == op_symbol
    })
  case found {
    Ok(item) -> {
      let #(_, op): #(String, Operator(a)) = item
      case op {
        Infix(_, _, _, _, constructor) -> {
          let new_first = constructor(first, right)
          fold_operators_multi(new_first, more, operators)
        }
        _ -> first
      }
    }
    Error(_) -> first
  }
}

// ============================================================================
// ALTERNATIVE CONSTRUCTION
// ============================================================================

pub fn alt(
  pattern: Pattern(a),
  constructor: fn(List(Value(a))) -> a,
) -> Alternative(a) {
  Alternative(pattern: pattern, constructor: constructor)
}

// ============================================================================
// PATTERN HELPERS
// ============================================================================

pub fn token_pattern(kind: String) -> Pattern(a) {
  TokenKind(kind)
}

pub fn keyword_pattern(value: String) -> Pattern(a) {
  Keyword(value)
}

pub fn ref(name: String) -> Pattern(a) {
  Ref(name)
}

pub fn seq(patterns: List(Pattern(a))) -> Pattern(a) {
  Seq(patterns)
}

/// Create a sequence with layout hints between elements
pub fn seq_with_layout(items: List(#(Pattern(a), LayoutHint))) -> Pattern(a) {
  SeqWithLayout(
    list.map(items, fn(item) {
      let #(pattern, hint) = item
      SeqItem(pattern, hint)
    }),
  )
}

pub fn choice(alts: List(Pattern(a))) -> Pattern(a) {
  Choice(alts)
}

pub fn opt(pattern: Pattern(a)) -> Pattern(a) {
  Opt(pattern)
}

pub fn many(pattern: Pattern(a)) -> Pattern(a) {
  Many(pattern)
}

pub fn sep1(item: Pattern(a), sep: Pattern(a)) -> Pattern(a) {
  Sep1(item, sep)
}

/// Create a delimited list pattern.
///
/// Parses: open item (sep item)* close
/// 
/// Supports:
/// - Empty lists: ()
/// - Single items: (x)
/// - Multiple items: (x, y, z)
///
/// Examples:
/// - Function args: delimited(LParen, Primary, Comma, RParen)
/// - Array literals: delimited(LBracket, Expr, Comma, RBracket)
/// - Record fields: delimited(LBrace, Field, Comma, RBrace)
/// - Block statements: delimited(LBrace, Stmt, Semi, RBrace)
pub fn delimited(
  open: Pattern(a),
  item: Pattern(a),
  sep: Pattern(a),
  close: Pattern(a),
) -> Pattern(a) {
  Delimited(open, item, sep, close)
}

pub fn parenthesized(rule_name: String) -> Pattern(a) {
  Parens(rule_name)
}

// ============================================================================
// OPERATOR CONSTRUCTION
// ============================================================================

/// Default operator layout
pub fn default_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(separator: separator)
}

/// Break before operator layout (like Haskell's $)
pub fn break_before_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(separator: separator)
}

/// Compact operator layout (never break)
pub fn compact_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(separator: separator)
}

// ============================================================================
// OPERATOR CONSTRUCTION HELPERS
// ============================================================================

/// Create prefix operator: <symbol> <expr>
/// Example: -x, !x, ~x
pub fn prefix(
  symbol: String,
  constructor: fn(a) -> a,
  precedence: Int,
) -> #(String, Operator(a)) {
  #(symbol, Prefix(precedence, symbol, constructor))
}

/// Create postfix operator: <expr> <symbol>
/// Example: x!, x++, x--
pub fn postfix(
  symbol: String,
  constructor: fn(a) -> a,
  precedence: Int,
) -> #(String, Operator(a)) {
  #(symbol, Postfix(precedence, symbol, constructor))
}

/// Create binary infix operator (no postfix): lhs <sep> rhs
/// Example: x + y, x = y, x |> y
pub fn infix_binary(
  symbol: String,
  constructor: fn(a, a) -> a,
  kind: OperatorKind,
  precedence: Int,
  separator: String,
) -> #(String, Operator(a)) {
  #(symbol, Infix(kind, precedence, separator, None, constructor))
}

/// Create wrapped infix operator (index, call): lhs <open> rhs <close>
/// Example: a[i], f(x), <x>
pub fn infix_wrapped(
  symbol: String,
  constructor: fn(a, a) -> a,
  kind: OperatorKind,
  precedence: Int,
  open: String,
  close: String,
) -> #(String, Operator(a)) {
  #(symbol, Infix(kind, precedence, open, Close(close), constructor))
}

/// Create ternary infix operator: lhs <infix_op> mid <sep> rhs
/// Example: a ? b : c, if a then b else c
pub fn infix_ternary(
  infix_symbol: String,
  constructor: fn(a, a) -> a,
  kind: OperatorKind,
  precedence: Int,
  sep1: String,
  sep2: String,
) -> #(String, Operator(a)) {
  #(
    infix_symbol,
    Infix(
      kind,
      precedence,
      infix_symbol,
      Continue(sep1, Close(sep2)),
      constructor,
    ),
  )
}

/// Create slice infix operator: lhs <open> start <sep> end <close>
/// Example: a[b:c], a[b..c]
pub fn infix_slice(
  open: String,
  constructor: fn(a, a) -> a,
  kind: OperatorKind,
  precedence: Int,
  sep: String,
  close: String,
) -> #(String, Operator(a)) {
  #(
    open,
    Infix(kind, precedence, open, Continue(sep, Close(close)), constructor),
  )
}

/// Create an operator with default layout (deprecated - use infix_binary)
pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
) -> #(String, Operator(a)) {
  #(keyword, Infix(InfixLeft, precedence, keyword, None, constructor))
}

/// Create an operator with custom layout (deprecated - use infix_wrapped)
pub fn op_with_layout(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
  layout: OperatorLayout,
) -> #(String, Operator(a)) {
  #(keyword, Infix(InfixLeft, precedence, layout.separator, None, constructor))
}

// ============================================================================
// PARSER
// ============================================================================

// Helper function that panics - used when grammar is malformed
// This has type `a` for any `a` because it never returns
fn panic_with_message(msg: String) -> a {
  panic as msg
}

pub fn parse(
  grammar: Grammar(a),
  source: String,
  error_ast: a,
) -> ParseResult(a) {
  let tokens = lexer.tokenize(source)
  let rule = case get_rule(grammar, grammar.start) {
    Ok(rule) -> rule
    Error(_) ->
      panic_with_message(
        "BUG: Grammar missing start rule '" <> grammar.start <> "'",
      )
  }
  case parse_rule(grammar, rule, tokens, 0) {
    Ok(#(ast, consumed_pos)) -> {
      // Check if there are unconsumed tokens
      case get_token(tokens, consumed_pos) {
        Ok(unexpected_token) -> {
          // There are remaining tokens that weren't consumed - this is an error
          let error = ParseError(
            span: Span("input", unexpected_token.start, unexpected_token.line, unexpected_token.column, unexpected_token.end),
            expected: "end of input",
            got: unexpected_token.value,
            context: "unexpected token after successful parse",
          )
          ParseResult(ast: error_ast, errors: [error])
        }
        Error(_) -> {
          // All tokens consumed successfully
          ParseResult(ast, [])
        }
      }
    }
    Error(e) -> ParseResult(ast: error_ast, errors: [e])
  }
}

fn get_rule(grammar: Grammar(a), name: String) -> Result(Rule(a), Nil) {
  list.find(grammar.rules, fn(rule) { rule.name == name })
  |> result.map_error(fn(_) { Nil })
}

fn parse_rule(
  grammar: Grammar(a),
  rule: Rule(a),
  tokens: List(Token),
  pos: Int,
) -> Result(#(a, Int), ParseError) {
  try_alternatives(grammar, rule.alternatives, tokens, pos)
}

fn try_alternatives(
  grammar: Grammar(a),
  alternatives: List(Alternative(a)),
  tokens: List(Token),
  pos: Int,
) -> Result(#(a, Int), ParseError) {
  case alternatives {
    [] -> Error(ParseError(span: Span("input", 0, 0, 0, 1), expected: "valid alternative", got: "none", context: ""))
    [alt, ..rest] -> {
      case parse_pattern(grammar, alt.pattern, tokens, pos) {
        Ok(#(values, new_pos)) -> {
          let ast = alt.constructor(values)
          Ok(#(ast, new_pos))
        }
        Error(_) -> try_alternatives(grammar, rest, tokens, pos)
      }
    }
  }
}

fn parse_pattern(
  grammar: Grammar(a),
  pattern: Pattern(a),
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value(a)), Int), Nil) {
  case pattern {
    TokenKind(kind) -> parse_token_kind(tokens, pos, kind)
    Keyword(value) -> parse_keyword(tokens, pos, value)
    Op(value) -> parse_op(tokens, pos, value)
    Ref(rule_name) -> parse_ref(grammar, rule_name, tokens, pos)
    Seq(patterns) -> parse_seq(grammar, patterns, tokens, pos, [])
    SeqWithLayout(items) ->
      parse_seq_with_layout(grammar, items, tokens, pos, [])
    Choice(alts) -> parse_choice(grammar, alts, tokens, pos)
    Opt(p) -> parse_opt(grammar, p, tokens, pos)
    Many(p) -> parse_many(grammar, p, tokens, pos, [])
    Sep1(item, sep) -> parse_sep1(grammar, item, sep, tokens, pos, [])
    Parens(rule_name) -> parse_parens(grammar, rule_name, tokens, pos)
    Delimited(open, item, sep, close) ->
      parse_delimited(grammar, open, item, sep, close, tokens, pos)
  }
}

fn parse_token_kind(
  tokens: List(Token),
  pos: Int,
  kind: String,
) -> Result(#(List(Value(a)), Int), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.kind == kind -> Ok(#([TokenValue(token)], pos + 1))
    _ -> Error(Nil)
  }
}

fn parse_keyword(
  tokens: List(Token),
  pos: Int,
  value: String,
) -> Result(#(List(Value(a)), Int), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.value == value -> Ok(#([KeywordValue(token)], pos + 1))
    _ -> Error(Nil)
  }
}

fn parse_op(
  tokens: List(Token),
  pos: Int,
  value: String,
) -> Result(#(List(Value(a)), Int), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.kind == "Operator" && token.value == value ->
      Ok(#([TokenValue(token)], pos + 1))
    _ -> Error(Nil)
  }
}

fn parse_ref(
  grammar: Grammar(a),
  rule_name: String,
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value(a)), Int), Nil) {
  case get_rule(grammar, rule_name) {
    Ok(rule) -> {
      case parse_rule(grammar, rule, tokens, pos) {
        Ok(#(ast, new_pos)) -> Ok(#([AstValue(ast)], new_pos))
        Error(_) -> Error(Nil)
      }
    }
    Error(_) -> Error(Nil)
  }
}

fn parse_seq(
  grammar: Grammar(a),
  patterns: List(Pattern(a)),
  tokens: List(Token),
  pos: Int,
  values: List(Value(a)),
) -> Result(#(List(Value(a)), Int), Nil) {
  case patterns {
    [] -> Ok(#(values, pos))
    [p, ..rest] -> {
      case parse_pattern(grammar, p, tokens, pos) {
        Ok(#(parsed, new_pos)) ->
          parse_seq(grammar, rest, tokens, new_pos, list.append(values, parsed))
        Error(_) -> Error(Nil)
      }
    }
  }
}

fn parse_seq_with_layout(
  grammar: Grammar(a),
  items: List(SeqItem(a)),
  tokens: List(Token),
  pos: Int,
  values: List(Value(a)),
) -> Result(#(List(Value(a)), Int), Nil) {
  case items {
    [] -> Ok(#(values, pos))
    [item, ..rest] -> {
      case parse_pattern(grammar, item.pattern, tokens, pos) {
        Ok(#(parsed, new_pos)) ->
          parse_seq_with_layout(
            grammar,
            rest,
            tokens,
            new_pos,
            list.append(values, parsed),
          )
        Error(_) -> Error(Nil)
      }
    }
  }
}

fn parse_choice(
  grammar: Grammar(a),
  alts: List(Pattern(a)),
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value(a)), Int), Nil) {
  case alts {
    [] -> Error(Nil)
    [alt, ..rest] -> {
      case parse_pattern(grammar, alt, tokens, pos) {
        Ok(#(values, new_pos)) -> Ok(#(values, new_pos))
        Error(_) -> parse_choice(grammar, rest, tokens, pos)
      }
    }
  }
}

fn parse_opt(
  grammar: Grammar(a),
  pattern: Pattern(a),
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value(a)), Int), Nil) {
  case parse_pattern(grammar, pattern, tokens, pos) {
    Ok(#(values, new_pos)) -> Ok(#(values, new_pos))
    Error(_) -> Ok(#([], pos))
  }
}

fn parse_many(
  grammar: Grammar(a),
  pattern: Pattern(a),
  tokens: List(Token),
  pos: Int,
  values: List(Value(a)),
) -> Result(#(List(Value(a)), Int), Nil) {
  case parse_pattern(grammar, pattern, tokens, pos) {
    Ok(#(parsed, new_pos)) ->
      parse_many(
        grammar,
        pattern,
        tokens,
        new_pos,
        list.append(values, [ListValue(parsed)]),
      )
    Error(_) -> Ok(#(values, pos))
  }
}

fn parse_sep1(
  grammar: Grammar(a),
  item: Pattern(a),
  sep: Pattern(a),
  tokens: List(Token),
  pos: Int,
  values: List(Value(a)),
) -> Result(#(List(Value(a)), Int), Nil) {
  case parse_pattern(grammar, item, tokens, pos) {
    Ok(#(first, new_pos)) ->
      parse_sep1_loop(
        grammar,
        item,
        sep,
        tokens,
        new_pos,
        list.append(values, first),
      )
    Error(_) -> Error(Nil)
  }
}

fn parse_sep1_loop(
  grammar: Grammar(a),
  item: Pattern(a),
  sep: Pattern(a),
  tokens: List(Token),
  pos: Int,
  values: List(Value(a)),
) -> Result(#(List(Value(a)), Int), Nil) {
  case parse_pattern(grammar, sep, tokens, pos) {
    Ok(#(_, sep_pos)) -> {
      case parse_pattern(grammar, item, tokens, sep_pos) {
        Ok(#(parsed, new_pos)) ->
          parse_sep1_loop(
            grammar,
            item,
            sep,
            tokens,
            new_pos,
            list.append(values, parsed),
          )
        Error(_) -> Ok(#(values, pos))
      }
    }
    Error(_) -> Ok(#(values, pos))
  }
}

fn parse_parens(
  grammar: Grammar(a),
  rule_name: String,
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value(a)), Int), Nil) {
  case parse_pattern(grammar, token_pattern("LParen"), tokens, pos) {
    Ok(#(_, lparen_pos)) -> {
      case parse_ref(grammar, rule_name, tokens, lparen_pos) {
        Ok(#(expr_values, expr_pos)) -> {
          case
            parse_pattern(grammar, token_pattern("RParen"), tokens, expr_pos)
          {
            Ok(#(_, rparen_pos)) ->
              Ok(#([ParensValue(expr_values)], rparen_pos))
            Error(_) -> Error(Nil)
          }
        }
        Error(_) -> Error(Nil)
      }
    }
    Error(_) -> Error(Nil)
  }
}

/// Parse a delimited list: open item (sep item)* close
///
/// Supports:
/// - Empty lists: ()
/// - Single items: (x)
/// - Multiple items: (x, y, z)
/// - Optional trailing separator: (x, y, z,)
fn parse_delimited(
  grammar: Grammar(a),
  open: Pattern(a),
  item: Pattern(a),
  sep: Pattern(a),
  close: Pattern(a),
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value(a)), Int), Nil) {
  // Parse opening token
  case parse_pattern(grammar, open, tokens, pos) {
    Ok(#(_, open_pos)) -> {
      // Try to parse items
      parse_delimited_items(grammar, item, sep, close, tokens, open_pos, [])
    }
    Error(_) -> Error(Nil)
  }
}

/// Parse items in a delimited list (after opening token)
fn parse_delimited_items(
  grammar: Grammar(a),
  item: Pattern(a),
  sep: Pattern(a),
  close: Pattern(a),
  tokens: List(Token),
  pos: Int,
  acc: List(Value(a)),
) -> Result(#(List(Value(a)), Int), Nil) {
  // First, try to parse the closing token (handles empty list or end of items)
  case parse_pattern(grammar, close, tokens, pos) {
    Ok(#(_, close_pos)) -> {
      // Successfully parsed closing token, return accumulated items
      Ok(#(acc, close_pos))
    }
    Error(_) -> {
      // Not a closing token, try to parse an item
      case parse_pattern(grammar, item, tokens, pos) {
        Ok(#(item_values, item_pos)) -> {
          // Successfully parsed an item, add to accumulator
          let new_acc = list.append(acc, item_values)
          // Now try to parse separator (required after item, unless it's the last)
          parse_delimited_after_item(
            grammar, item, sep, close, tokens, item_pos, new_acc,
          )
        }
        Error(_) -> {
          // Can't parse item and can't parse close - parse error
          Error(Nil)
        }
      }
    }
  }
}

/// Parse after an item in a delimited list
/// Try separator + more items, or just closing token
fn parse_delimited_after_item(
  grammar: Grammar(a),
  item: Pattern(a),
  sep: Pattern(a),
  close: Pattern(a),
  tokens: List(Token),
  pos: Int,
  acc: List(Value(a)),
) -> Result(#(List(Value(a)), Int), Nil) {
  // Try to parse separator
  case parse_pattern(grammar, sep, tokens, pos) {
    Ok(#(_, sep_pos)) -> {
      // Successfully parsed separator, try to parse another item
      // (or closing token for trailing separator support)
      parse_delimited_items(
        grammar, item, sep, close, tokens, sep_pos, acc,
      )
    }
    Error(_) -> {
      // No separator, try closing token
      case parse_pattern(grammar, close, tokens, pos) {
        Ok(#(_, close_pos)) -> {
          // Successfully parsed closing token
          Ok(#(acc, close_pos))
        }
        Error(_) -> {
          // No separator and no closing token - parse error
          Error(Nil)
        }
      }
    }
  }
}

fn get_token(tokens: List(Token), pos: Int) -> Result(Token, Nil) {
  let dropped = list.drop(tokens, pos)
  case dropped {
    [token, ..] -> Ok(token)
    [] -> Error(Nil)
  }
}

// ============================================================================
// POSITION HELPERS
// ============================================================================

/// Helper functions for extracting source positions from parsed values.
/// Use these in grammar constructors to create accurate spans.
/// Extract span from first token in values
pub fn span_from_values(values: List(Value(a)), filename: String) -> Span {
  case values {
    [TokenValue(token), ..] -> span_from_token(token, filename)
    [AstValue(_), ..] -> Span(filename, 1, 1, 1, 1)
    // Default for AST values
    _ -> Span(filename, 1, 1, 1, 1)
    // Default
  }
}

/// Create span from single token
pub fn span_from_token(token: lexer.Token, filename: String) -> Span {
  Span(
    file: filename,
    start_line: token.line,
    start_col: token.column,
    end_line: token.line,
    end_col: token.column + string.length(token.value),
  )
}

/// Create span covering first and last token
pub fn span_from_tokens(
  first: lexer.Token,
  last: lexer.Token,
  filename: String,
) -> Span {
  Span(
    file: filename,
    start_line: first.line,
    start_col: first.column,
    end_line: last.line,
    end_col: last.column + string.length(last.value),
  )
}

/// Extract first token from values
pub fn first_token(values: List(Value(a))) -> Result(lexer.Token, Nil) {
  case values {
    [TokenValue(token), ..] -> Ok(token)
    _ -> Error(Nil)
  }
}

/// Extract last token from values (recursively)
pub fn last_token(values: List(Value(a))) -> Result(lexer.Token, Nil) {
  case values {
    [] -> Error(Nil)
    [TokenValue(token)] -> Ok(token)
    [TokenValue(token), ListValue(rest), ..] -> {
      case last_token(rest) {
        Ok(last) -> Ok(last)
        Error(_) -> Ok(token)
      }
    }
    [_, ..rest] -> last_token(rest)
  }
}

/// Get span for entire value list
pub fn span_from_value_list(values: List(Value(a)), filename: String) -> Span {
  case first_token(values), last_token(values) {
    Ok(first), Ok(last) -> span_from_tokens(first, last, filename)
    Ok(first), Error(_) -> span_from_token(first, filename)
    Error(_), Ok(last) -> span_from_token(last, filename)
    Error(_), Error(_) -> Span(filename, 1, 1, 1, 1)
  }
}

/// Create a dummy span for testing or placeholder use
///
/// Use this when span information is not available or not needed.
/// Example: creating synthetic terms during desugaring
pub fn dummy_span() -> Span {
  Span("input", 0, 0, 0, 0)
}

/// Create a span from a single position
///
/// Use this when you have a specific line/column but no end position.
/// Example: reporting an error at a specific location
pub fn mk_span(file: String, line: Int, col: Int) -> Span {
  Span(file, line, col, line, col)
}

// ============================================================================
// QUERY API
// ============================================================================

/// Get operator by symbol from grammar
///
/// Example:
/// ```gleam
/// case get_operator(grammar, "+") {
///   Ok(op) -> // use operator metadata
///   Error(_) -> // operator not found
/// }
/// ```
pub fn get_operator(
  grammar: Grammar(a),
  symbol: String,
) -> Result(Operator(a), Nil) {
  list.key_find(grammar.operators, symbol)
}

/// Get operator precedence by symbol
pub fn get_operator_precedence(grammar: Grammar(a), symbol: String) -> Int {
  case get_operator(grammar, symbol) {
    Ok(op) -> {
      case op {
        Prefix(prec, _, _) -> prec
        Postfix(prec, _, _) -> prec
        Infix(_, prec, _, _, _) -> prec
      }
    }
    Error(_) -> 0
  }
}

/// Get operator kind by symbol
pub fn get_operator_kind(
  grammar: Grammar(a),
  symbol: String,
) -> Result(OperatorKind, Nil) {
  case get_operator(grammar, symbol) {
    Ok(op) -> {
      case op {
        Prefix(_, _, _) -> Ok(KindPrefix)
        Postfix(_, _, _) -> Ok(KindPostfix)
        Infix(kind, _, _, _, _) -> Ok(kind)
      }
    }
    Error(_) -> Error(Nil)
  }
}

// ============================================================================
// FORMATTER METADATA EXTRACTION (deprecated - use get_operator)
// ============================================================================
/// Extract operator precedence table from grammar.
///
/// Returns a function that can lookup precedence by operator name.
///
/// Example:
/// ```gleam
/// let get_prec = grammar.extract_precedence_table(calc_grammar())
/// get_prec("+")  // Ok(10)
/// get_prec("*")  // Ok(20)
/// ```
pub fn extract_precedence_table(
  grammar: Grammar(a),
) -> fn(String) -> Result(Int, Nil) {
  let operators = grammar.operators

  fn(op_name: String) -> Result(Int, Nil) {
    let found =
      list.find(operators, fn(item) {
        let #(sym, _) = item
        sym == op_name
      })
    case found {
      Ok(item) -> {
        let #(_, op): #(String, Operator(a)) = item
        case op {
          Prefix(prec, _, _) -> Ok(prec)
          Postfix(prec, _, _) -> Ok(prec)
          Infix(_, prec, _, _, _) -> Ok(prec)
        }
      }
      Error(_) -> Error(Nil)
    }
  }
}

/// Extract operator layout table from grammar.
///
/// Returns a function that can lookup layout by operator name.
///
/// Example:
/// ```gleam
/// let get_layout = grammar.extract_layout_table(calc_grammar())
/// get_layout("+")  // Ok(OperatorLayout(" + "))
/// ```
pub fn extract_layout_table(
  grammar: Grammar(a),
) -> fn(String) -> Result(OperatorLayout, Nil) {
  let operators = grammar.operators

  fn(op_name: String) -> Result(OperatorLayout, Nil) {
    let found =
      list.find(operators, fn(item) {
        let #(sym, _) = item
        sym == op_name
      })
    case found {
      Ok(item) -> {
        let #(_, op): #(String, Operator(a)) = item
        case op {
          Infix(_, _, infix_op, _, _) -> Ok(OperatorLayout(infix_op))
          Prefix(_, symbol, _) -> Ok(OperatorLayout(symbol))
          Postfix(_, symbol, _) -> Ok(OperatorLayout(symbol))
        }
      }
      Error(_) -> Error(Nil)
    }
  }
}

/// Extract constructor precedence from grammar.
///
/// Returns a function that can lookup precedence by constructor name.
/// Requires a mapping from constructor names to operator names.
///
/// Example:
/// ```gleam
/// let ctor_map = dict.from_list([#("Add", "+"), #("Mul", "*")])
/// let get_prec = grammar.extract_constructor_precedence(calc_grammar(), ctor_map)
/// get_prec("Add")  // Ok(10)
/// get_prec("Mul")  // Ok(20)
/// ```
pub fn extract_constructor_precedence(
  grammar: Grammar(a),
  constructor_map: Dict(String, String),
) -> fn(String) -> Result(Int, Nil) {
  let precedence_table = extract_precedence_table(grammar)

  fn(ctor_name: String) -> Result(Int, Nil) {
    case dict.get(constructor_map, ctor_name) {
      Ok(op_name) -> precedence_table(op_name)
      Error(_) -> Error(Nil)
    }
  }
}

// ============================================================================
// FORMATTER - User-Provided
// ============================================================================

// ============================================================================
// GRAMMAR-BASED FORMATTER HELPERS
// ============================================================================

/// Get precedence for a constructor from grammar.
///
/// Looks up the constructor by finding the operator with matching constructor function.
/// Returns 0 if not found (for non-operator constructors).
///
/// Note: This uses function reference equality, which works for named functions.
/// For anonymous functions, you may need to provide a mapping.
pub fn get_precedence_for_constructor(
  grammar: Grammar(a),
  constructor_key: #(String, fn(a, a) -> a),
) -> Int {
  let constructor_fn = constructor_key.1
  case
    list.find(grammar.operators, fn(item) {
      let #(_, op) = item
      case op {
        Infix(_, _, _, _, c) -> c == constructor_fn
        Prefix(_, _, _) -> False
        Postfix(_, _, _) -> False
      }
    })
  {
    Ok(item) -> {
      let #(_, op) = item
      case op {
        Infix(_, prec, _, _, _) -> prec
        Prefix(prec, _, _) -> prec
        Postfix(prec, _, _) -> prec
      }
    }
    Error(_) -> 0
  }
}

/// Get operator symbol for a constructor from grammar.
pub fn get_operator_symbol_for_constructor(
  grammar: Grammar(a),
  constructor_key: #(String, fn(a, a) -> a),
) -> String {
  let constructor_fn = constructor_key.1
  case
    list.find(grammar.operators, fn(item) {
      let #(_, op) = item
      case op {
        Infix(_, _, _, _, c) -> c == constructor_fn
        Prefix(_, _, _) -> False
        Postfix(_, _, _) -> False
      }
    })
  {
    Ok(item) -> {
      let #(_, op) = item
      case op {
        Infix(_, _, infix_op, _, _) -> infix_op
        Prefix(_, symbol, _) -> symbol
        Postfix(_, symbol, _) -> symbol
      }
    }
    Error(_) -> ""
  }
}

/// Format binary operator with precedence extracted from grammar.
///
/// This ensures precedence is defined ONCE in the grammar and reused by the formatter.
///
/// Example:
/// ```gleam
/// fn format_expr(ast: Expr, parent_prec: Int, grammar: Grammar(Expr)) -> Doc {
///   case ast {
///     Add(l, r) ->
///       format_binop_with_grammar(
///         grammar,
///         format_expr,
///         l,
///         r,
///         #("Add", make_add),  // Constructor key to look up in grammar
///         parent_prec,
///       )
///   }
/// }
/// ```
pub fn format_binop_with_grammar(
  grammar: Grammar(a),
  format_fn: fn(a, Int, Grammar(a)) -> Doc,
  left: a,
  right: a,
  constructor_key: #(String, fn(a, a) -> a),
  parent_prec: Int,
) -> Doc {
  let prec = get_precedence_for_constructor(grammar, constructor_key)
  let left_doc = format_fn(left, prec, grammar)
  let right_doc = format_fn(right, prec + 1, grammar)
  let separator = get_operator_symbol_for_constructor(grammar, constructor_key)

  let doc = concat([left_doc, text(" "), text(separator), text(" "), right_doc])

  case prec < parent_prec {
    True -> parens(doc)
    False -> doc
  }
}
