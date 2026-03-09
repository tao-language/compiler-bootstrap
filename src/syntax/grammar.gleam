// ============================================================================
// GRAMMAR - Unified Grammar DSL
// ============================================================================
import gleam/dict.{type Dict}
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/formatter.{type Doc}
import syntax/lexer.{type Token}

// ============================================================================
// TYPES
// ============================================================================

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

fn fold_operators(
  first: a,
  rest_values: List(Value(a)),
  apply: fn(a, a) -> a,
) -> a {
  case rest_values {
    [] -> first
    [op_right, ..more] -> {
      case op_right {
        ListValue([TokenValue(_), AstValue(right)]) -> {
          let new_first = apply(first, right)
          fold_operators(new_first, more, apply)
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
      )
    })
  let first_alt =
    alt(ref(first_rule), fn(values) {
      case values {
        [AstValue(first)] -> first
        _ -> panic as "right_assoc: expected single value"
      }
    })
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
  case dict.get(grammar.rules, grammar.start) {
    Ok(rule) -> {
      case parse_rule(grammar, rule, tokens, 0) {
        Ok(#(ast, _)) -> ParseResult(ast: ast, errors: [])
        Error(err) -> ParseResult(ast: panic as "Parse failed", errors: [err])
      }
    }
    Error(_) ->
      ParseResult(ast: panic as "No start rule", errors: [
        ParseError(position: 0, expected: "start rule", got: "none"),
      ])
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
// FORMATTER - Generated from Grammar
// ============================================================================

/// Format an AST using grammar rules.
/// The grammar is the single source of truth - it defines both
/// how to parse (constructors) and how to format (deconstructors).
pub fn format(grammar: Grammar(a), ast: a) -> String {
  format_ast(grammar, ast, -1) |> formatter.render_default
}

pub fn format_with_width(grammar: Grammar(a), ast: a, width: Int) -> String {
  format_ast(grammar, ast, -1) |> formatter.render(width)
}

/// Format an AST with precedence for parenthesization
fn format_ast(grammar, ast, parent_prec) -> Doc {
  // Find matching alternative by trying each rule's formatters
  let match_result =
    list.find_map(grammar.rules, fn(rule) {
      list.find_map(rule.alternatives, fn(alt) {
        // Try the formatter - it returns the formatted doc
        Some(alt.formatter(ast, parent_prec))
      })
    })

  case match_result {
    Some(doc) -> doc
    None -> formatter.text("<unknown>")
  }
}

/// Format values according to pattern with layout hints
fn format_pattern(
  grammar: Grammar(a),
  pattern: Pattern(a),
  values: List(Value(a)),
  parent_prec: Int,
  rule_prec: Int,
) -> Doc {
  case pattern {
    TokenKind(_) -> format_token_value(values)
    Keyword(_) -> format_token_value(values)
    Op(_) -> format_token_value(values)
    Ref(_) -> format_ref_value(grammar, values, parent_prec)
    Seq(patterns) -> format_seq(grammar, patterns, values, parent_prec)
    SeqWithLayout(items) ->
      format_seq_with_layout(grammar, items, values, parent_prec, rule_prec)
    Choice(_) -> format_choice_value(grammar, values, parent_prec)
    Opt(p) -> format_opt(grammar, p, values, parent_prec)
    Many(p) -> format_many(grammar, p, values, parent_prec)
    Sep1(item, sep) -> format_sep1(grammar, item, sep, values, parent_prec)
    Parens(rule) -> format_parens(grammar, rule, values, parent_prec)
  }
}

fn format_token_value(values: List(Value(a))) -> Doc {
  case values {
    [TokenValue(token)] -> formatter.text(token.value)
    _ -> formatter.text("<token>")
  }
}

fn format_ref_value(
  grammar: Grammar(a),
  values: List(Value(a)),
  parent_prec,
) -> Doc {
  case values {
    [AstValue(ast)] -> format_ast(grammar, ast, parent_prec)
    _ -> formatter.text("<ref>")
  }
}

fn format_seq(
  grammar: Grammar(a),
  patterns: List(Pattern(a)),
  values: List(Value(a)),
  parent_prec: Int,
) -> Doc {
  let docs = format_seq_loop(grammar, patterns, values, parent_prec, [])
  formatter.concat(list.reverse(docs))
}

fn format_seq_loop(
  grammar: Grammar(a),
  patterns: List(Pattern(a)),
  values: List(Value(a)),
  parent_prec: Int,
  docs: List(Doc),
) -> List(Doc) {
  case patterns, values {
    [p, ..ps], [v, ..vs] -> {
      let doc = format_pattern(grammar, p, [v], parent_prec, 0)
      format_seq_loop(grammar, ps, vs, parent_prec, [doc, ..docs])
    }
    _, _ -> docs
  }
}

fn format_seq_with_layout(
  grammar: Grammar(a),
  items: List(SeqItem(a)),
  values: List(Value(a)),
  parent_prec: Int,
  rule_prec: Int,
) -> Doc {
  let docs =
    format_seq_with_layout_loop(
      grammar,
      items,
      values,
      parent_prec,
      rule_prec,
      [],
    )
  formatter.concat(list.reverse(docs))
}

fn format_seq_with_layout_loop(
  grammar: Grammar(a),
  items: List(SeqItem(a)),
  values: List(Value(a)),
  parent_prec: Int,
  rule_prec: Int,
  docs: List(Doc),
) -> List(Doc) {
  case items, values {
    [item, ..items], [v, ..vs] -> {
      let doc =
        format_pattern(grammar, item.pattern, [v], parent_prec, rule_prec)
      let sep = case item.layout_hint {
        SoftBreak -> formatter.line()
        HardBreak -> formatter.hardline()
        Space -> formatter.space()
        NoSeparator -> formatter.empty()
      }
      format_seq_with_layout_loop(grammar, items, vs, parent_prec, rule_prec, [
        sep,
        doc,
        ..docs
      ])
    }
    _, _ -> docs
  }
}

fn format_choice_value(
  grammar: Grammar(a),
  values: List(Value(a)),
  parent_prec,
) -> Doc {
  case values {
    [v] -> format_pattern_value(grammar, v, parent_prec)
    _ -> formatter.text("<choice>")
  }
}

fn format_opt(
  grammar: Grammar(a),
  pattern: Pattern(a),
  values: List(Value(a)),
  parent_prec,
) -> Doc {
  case values {
    [] -> formatter.empty()
    [v] -> format_pattern(grammar, pattern, [v], parent_prec, 0)
  }
}

fn format_many(
  grammar: Grammar(a),
  pattern: Pattern(a),
  values: List(Value(a)),
  parent_prec,
) -> Doc {
  let docs =
    list.map(values, fn(v) {
      format_pattern(grammar, pattern, [v], parent_prec, 0)
    })
  formatter.concat(docs)
}

fn format_sep1(
  grammar: Grammar(a),
  item: Pattern(a),
  sep: Pattern(a),
  values: List(Value(a)),
  parent_prec: Int,
) -> Doc {
  case values {
    [] -> formatter.empty()
    [first] -> format_pattern(grammar, item, [first], parent_prec, 0)
    [first, ..rest] -> {
      let first_doc = format_pattern(grammar, item, [first], parent_prec, 0)
      let rest_docs =
        list.map(rest, fn(v) {
          let sep_doc = format_pattern(grammar, sep, [], parent_prec, 0)
          let item_doc = format_pattern(grammar, item, [v], parent_prec, 0)
          formatter.concat([sep_doc, item_doc])
        })
      formatter.concat([first_doc, formatter.concat(rest_docs)])
    }
  }
}

fn format_parens(
  grammar: Grammar(a),
  rule: String,
  values: List(Value(a)),
  parent_prec,
) -> Doc {
  case values {
    [v] -> {
      let inner = format_pattern_value(grammar, v, parent_prec)
      formatter.parens(inner)
    }
    _ -> formatter.text("<parens>")
  }
}

fn format_pattern_value(
  grammar: Grammar(a),
  value: Value(a),
  parent_prec,
) -> Doc {
  case value {
    TokenValue(token) -> formatter.text(token.value)
    AstValue(ast) -> format_ast(grammar, ast, parent_prec)
    ListValue(values) ->
      formatter.concat(
        list.map(values, fn(v) { format_pattern_value(grammar, v, parent_prec) }),
      )
    KeywordValue(token) -> formatter.text(token.value)
  }
}

pub fn format_binop(
  left: Doc,
  right: Doc,
  separator: String,
  precedence: Int,
  parent_prec: Int,
  layout: LayoutStyle,
) -> Doc {
  let inner = case layout {
    Inline -> concat([left, text(separator), right])
    BreakAfterOperator(indent) ->
      group(concat([left, text(separator), line(), nest(indent, right)]))
    BreakBeforeOperator(indent) ->
      group(
        concat([left, line(), nest(indent, concat([text(separator), right]))]),
      )
    Block(open, close, indent) ->
      group(
        concat([
          text(open),
          nest(
            indent,
            concat([hardline(), left, text(separator), hardline(), right]),
          ),
          text(close),
        ]),
      )
  }
  wrap_parens(inner, precedence < parent_prec)
}

fn concat(docs: List(Doc)) -> Doc {
  formatter.concat(docs)
}

fn text(s: String) -> Doc {
  formatter.text(s)
}

fn line() -> Doc {
  formatter.line()
}

fn hardline() -> Doc {
  formatter.hardline()
}

fn group(doc: Doc) -> Doc {
  formatter.group(doc)
}

fn nest(n: Int, doc: Doc) -> Doc {
  formatter.nest(n, doc)
}

fn wrap_parens(doc: Doc, condition: Bool) -> Doc {
  case condition {
    True -> formatter.parens(doc)
    False -> doc
  }
}

// ============================================================================
// GENERIC FORMATTER HELPERS
// ============================================================================
// These helpers use grammar metadata for formatting, enabling automatic
// precedence-based parenthesization and separator formatting.

/// Default formatter configuration
pub fn default_formatter_config() -> FormatterConfig {
  FormatterConfig(width: 80, indent_string: "  ", indent_level: 0)
}

/// Format a binary operator using grammar metadata
pub fn format_binary_op(
  grammar: Grammar(a),
  op_name: String,
  left: a,
  right: a,
  parent_prec: Int,
  format_ast: fn(a, Int) -> Doc,
) -> Doc {
  case dict.get(grammar.operators, op_name) {
    Ok(op) -> {
      // Calculate precedence for left and right operands based on associativity
      let left_prec_offset = case op.associativity {
        Left -> 0
        Right -> 1
        NonAssoc -> 1
      }
      let right_prec_offset = case op.associativity {
        Left -> 1
        Right -> 0
        NonAssoc -> 1
      }

      let left_prec = op.precedence + left_prec_offset
      let right_prec = op.precedence + right_prec_offset

      let left_doc = format_ast(left, left_prec)

      // Format separator with spaces around operator
      let separator_doc = formatter.text(" " <> op.layout.separator <> " ")

      // Format right side with potential indentation
      let right_doc = case op.layout.indent_rhs {
        True -> formatter.nest(1, format_ast(right, right_prec))
        False -> format_ast(right, right_prec)
      }

      let inner =
        formatter.concat([
          left_doc,
          separator_doc,
          right_doc,
        ])

      // Add parentheses if operator precedence < parent precedence
      case op.precedence < parent_prec {
        True -> formatter.parens(inner)
        False -> inner
      }
    }
    Error(_) -> formatter.text("<unknown op: " <> op_name <> ">")
  }
}

/// Format a sequence with layout hints
pub fn format_sequence_with_layout(
  items: List(SeqItem(a)),
  values: List(Value(a)),
  format_value: fn(Value(a)) -> Doc,
) -> Doc {
  format_sequence_loop(items, values, format_value, [])
}

fn format_sequence_loop(
  items: List(SeqItem(a)),
  values: List(Value(a)),
  format_value: fn(Value(a)) -> Doc,
  docs: List(Doc),
) -> Doc {
  case items, values {
    [item, ..rest_items], [value, ..rest_values] -> {
      let doc = format_value(value)
      let separator = case item.layout_hint {
        SoftBreak -> formatter.line()
        HardBreak -> formatter.hardline()
        Space -> formatter.space()
        NoSeparator -> formatter.empty()
      }
      format_sequence_loop(
        rest_items,
        rest_values,
        format_value,
        list.append(docs, [doc, separator]),
      )
    }
    [], [] -> formatter.concat(docs)
    _, _ -> formatter.concat(docs)
    // Mismatch, just format what we have
  }
}

/// Format an atom (number, identifier, etc.)
pub fn format_atom(value: String) -> Doc {
  formatter.text(value)
}

/// Format a parenthesized expression
pub fn format_parenthesized(inner: Doc) -> Doc {
  formatter.parens(inner)
}
