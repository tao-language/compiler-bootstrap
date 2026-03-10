// ============================================================================
// GRAMMAR - Unified Grammar DSL
// ============================================================================
import gleam/dict.{type Dict}
import gleam/int
import gleam/list
import gleam/string
import syntax/formatter.{type Doc}
import syntax/lexer.{type Token}

// ============================================================================
// TYPES
// ============================================================================

/// Source location span
pub type Span {
  Span(
    file: String,
    start_line: Int,    // 1-based
    start_col: Int,     // 1-based
    end_line: Int,      // 1-based
    end_col: Int,       // 1-based
  )
}

pub type Associativity {
  Left
  Right
  NonAssoc
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

/// Layout configuration for operators
pub type OperatorLayout {
  OperatorLayout(
    separator: String,
    break_before: Bool,
    break_after: Bool,
    indent_rhs: Bool,
  )
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
}

pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,
    deconstructor: fn(a) -> List(Value(a)),
    formatter: fn(a, Int) -> Doc,
  )
}

pub type Rule(a) {
  Rule(name: String, alternatives: List(Alternative(a)), precedence: Int)
}

pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,
    precedence: Int,
    associativity: Associativity,
    layout: OperatorLayout,
  )
}

pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule(a)),
    tokens: List(String),
    keywords: List(String),
    operators: Dict(String, Operator(a)),
  )
}

pub type GrammarBuilder(a) {
  GrammarBuilder(
    name: String,
    start: String,
    rules: List(Rule(a)),
    tokens: List(String),
    keywords: List(String),
    operators: List(Operator(a)),
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
  ParseError(position: Int, expected: String, got: String)
}

pub type ParseResult(a) {
  ParseResult(ast: a, errors: List(ParseError))
}

// ============================================================================
// GRAMMAR DEFINITION API
// ============================================================================

pub fn define(
  builder_fn: fn(GrammarBuilder(a)) -> GrammarBuilder(a),
) -> Grammar(a) {
  let empty =
    GrammarBuilder(
      name: "Grammar",
      start: "Start",
      rules: [],
      tokens: [],
      keywords: [],
      operators: [],
    )
  let builder = builder_fn(empty)
  to_grammar(builder)
}

fn to_grammar(builder: GrammarBuilder(a)) -> Grammar(a) {
  let rules_dict =
    list.fold(builder.rules, dict.new(), fn(acc, rule) {
      dict.insert(acc, rule.name, rule)
    })
  let operators_dict =
    list.fold(builder.operators, dict.new(), fn(acc, op) {
      dict.insert(acc, op.keyword, op)
    })
  Grammar(
    name: builder.name,
    start: builder.start,
    rules: rules_dict,
    tokens: builder.tokens,
    keywords: builder.keywords,
    operators: operators_dict,
  )
}

pub fn name(builder: GrammarBuilder(a), name: String) -> GrammarBuilder(a) {
  GrammarBuilder(..builder, name: name)
}

pub fn start(builder: GrammarBuilder(a), rule: String) -> GrammarBuilder(a) {
  GrammarBuilder(..builder, start: rule)
}

pub fn token(builder: GrammarBuilder(a), kind: String) -> GrammarBuilder(a) {
  GrammarBuilder(..builder, tokens: [kind, ..builder.tokens])
}

pub fn keyword(builder: GrammarBuilder(a), kw: String) -> GrammarBuilder(a) {
  GrammarBuilder(..builder, keywords: [kw, ..builder.keywords])
}

pub fn rule(
  builder: GrammarBuilder(a),
  name: String,
  alternatives: List(Alternative(a)),
) -> GrammarBuilder(a) {
  let rule = Rule(name: name, alternatives: alternatives, precedence: 0)
  GrammarBuilder(..builder, rules: [rule, ..builder.rules])
}

pub fn left_assoc(
  builder: GrammarBuilder(a),
  name: String,
  first_rule: String,
  operators: List(Operator(a)),
  precedence: Int,
) -> GrammarBuilder(a) {
  let op_alt = create_operator_pattern(operators, first_rule)
  let rule = Rule(name: name, alternatives: [op_alt], precedence: precedence)
  let builder = GrammarBuilder(..builder, rules: [rule, ..builder.rules])
  list.fold(operators, builder, fn(b, op) {
    GrammarBuilder(..b, operators: [op, ..b.operators])
  })
}

fn create_operator_pattern(
  operators: List(Operator(a)),
  first_rule: String,
) -> Alternative(a) {
  let op_choice =
    Choice(
      list.map(operators, fn(op) { Seq([Op(op.keyword), Ref(first_rule)]) }),
    )
  let pattern =
    Seq([
      Ref(first_rule),
      Many(op_choice),
    ])
  Alternative(
    pattern: pattern,
    constructor: fn(values) {
      case values {
        [AstValue(first), ..rest] -> {
          fold_operators_multi(first, rest, operators)
        }
        _ -> panic as "left_assoc constructor: unexpected values"
      }
    },
    deconstructor: fn(_) { panic as "Deconstructor not implemented" },
    formatter: fn(_ast, _) { formatter.text("<ast>") },
  )
}

fn fold_operators_multi(
  first: a,
  rest_values: List(Value(a)),
  operators: List(Operator(a)),
) -> a {
  case rest_values {
    [] -> first
    [op_right, ..more] -> {
      case op_right {
        ListValue([TokenValue(op_token), AstValue(right)]) -> {
          case list.find(operators, fn(op) { op.keyword == op_token.value }) {
            Ok(op) -> {
              let new_first = op.constructor(first, right)
              fold_operators_multi(new_first, more, operators)
            }
            Error(_) -> first
          }
        }
        _ -> first
      }
    }
  }
}

pub fn right_assoc(
  builder: GrammarBuilder(a),
  name: String,
  first_rule: String,
  operators: List(Operator(a)),
  precedence: Int,
) -> GrammarBuilder(a) {
  let op_alts =
    list.map(operators, fn(op) {
      let pattern = Seq([Ref(first_rule), Keyword(op.keyword), Ref(name)])
      Alternative(
        pattern: pattern,
        constructor: fn(values) {
          case values {
            [AstValue(left), KeywordValue(_), AstValue(right)] ->
              op.constructor(left, right)
            _ -> panic as "right_assoc: expected 3 values"
          }
        },
        deconstructor: fn(_) { panic as "Deconstructor not implemented" },
        formatter: fn(_ast, _) { formatter.text("<ast>") },
      )
    })
  let first_alt =
    alt(
      ref(first_rule),
      fn(values) {
        case values {
          [AstValue(first)] -> first
          _ -> panic as "right_assoc: expected single value"
        }
      },
      fn(_ast, _) { formatter.text("<ast>") },
    )
  let rule =
    Rule(
      name: name,
      alternatives: [first_alt, ..op_alts],
      precedence: precedence,
    )
  let builder = GrammarBuilder(..builder, rules: [rule, ..builder.rules])
  list.fold(operators, builder, fn(b, op) {
    GrammarBuilder(..b, operators: [op, ..b.operators])
  })
}

// ============================================================================
// ALTERNATIVE CONSTRUCTION
// ============================================================================

pub fn alt(
  pattern: Pattern(a),
  constructor: fn(List(Value(a))) -> a,
  formatter: fn(a, Int) -> Doc,
) -> Alternative(a) {
  Alternative(
    pattern: pattern,
    constructor: constructor,
    deconstructor: fn(_) { panic as "Deconstructor not provided" },
    formatter: formatter,
  )
}

pub fn alt_with_deconstructor(
  pattern: Pattern(a),
  constructor: fn(List(Value(a))) -> a,
  deconstructor: fn(a) -> List(Value(a)),
  formatter: fn(a, Int) -> Doc,
) -> Alternative(a) {
  Alternative(
    pattern: pattern,
    constructor: constructor,
    deconstructor: deconstructor,
    formatter: formatter,
  )
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

pub fn parenthesized(rule_name: String) -> Pattern(a) {
  Parens(rule_name)
}

// ============================================================================
// OPERATOR CONSTRUCTION
// ============================================================================

/// Default operator layout (break after operator, indent RHS)
pub fn default_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(
    separator: separator,
    break_before: False,
    break_after: False,
    indent_rhs: False,
  )
}

/// Break before operator layout (like Haskell's $)
pub fn break_before_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(
    separator: separator,
    break_before: True,
    break_after: False,
    indent_rhs: False,
  )
}

/// Compact operator layout (never break)
pub fn compact_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(
    separator: separator,
    break_before: False,
    break_after: False,
    indent_rhs: False,
  )
}

pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
  layout: OperatorLayout,
) -> Operator(a) {
  Operator(
    keyword: keyword,
    constructor: constructor,
    precedence: precedence,
    associativity: Left,
    layout: layout,
  )
}

pub fn op_with_layout(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
  layout: OperatorLayout,
) -> Operator(a) {
  Operator(
    keyword: keyword,
    constructor: constructor,
    precedence: precedence,
    associativity: Left,
    layout: layout,
  )
}

// ============================================================================
// PARSER
// ============================================================================

pub fn parse(grammar: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(source)
  let rule = case dict.get(grammar.rules, grammar.start) {
    Ok(rule) -> rule
    Error(_) -> panic as "Grammar missing start rule"
  }
  case parse_rule(grammar, rule, tokens, 0) {
    Ok(#(ast, _)) -> ParseResult(ast: ast, errors: [])
    Error(parse_error) -> {
      // Report parse error and panic - caller should check for errors first
      let error_msg = parse_error_to_string(parse_error)
      panic as "Parse error: " <> error_msg
      // Never returns, but type system needs this
      ParseResult(panic as "unreachable", [])
    }
  }
}

fn parse_error_to_string(err: ParseError) -> String {
  case err {
    ParseError(position: pos, expected: exp, got: g) ->
      "At position " <> int.to_string(pos) <> ": expected " <> exp <> ", got " <> g
  }
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
    [] ->
      Error(ParseError(
        position: pos,
        expected: "valid alternative",
        got: "none",
      ))
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
  case dict.get(grammar.rules, rule_name) {
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
    [AstValue(_), ..] -> Span(filename, 1, 1, 1, 1)  // Default for AST values
    _ -> Span(filename, 1, 1, 1, 1)  // Default
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
pub fn span_from_value_list(
  values: List(Value(a)),
  filename: String,
) -> Span {
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
// FORMATTER - User-Provided
// ============================================================================
