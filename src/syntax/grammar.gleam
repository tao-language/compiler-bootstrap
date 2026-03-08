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

pub type LayoutStyle {
  Inline
  BreakAfterOperator(indent: Int)
  BreakBeforeOperator(indent: Int)
  Block(open: String, close: String, indent: Int)
}

pub type Pattern {
  TokenKind(kind: String)
  Keyword(value: String)
  Ref(rule: String)
  Seq(patterns: List(Pattern))
  Choice(alts: List(Pattern))
  Opt(pattern: Pattern)
  Many(pattern: Pattern)
  Sep1(item: Pattern, sep: Pattern)
  Parens(rule: String)
}

pub type Alternative(a) {
  Alternative(pattern: Pattern, constructor: fn(List(Value(a))) -> a)
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
    layout: LayoutStyle,
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
  let op_alts = create_operator_alternatives(operators, first_rule)
  let first_alt =
    alt(ref(first_rule), fn(values) {
      case values {
        [AstValue(first)] -> first
        _ -> panic as "left_assoc: expected single value"
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

fn create_operator_alternatives(
  operators: List(Operator(a)),
  first_rule: String,
) -> List(Alternative(a)) {
  list.map(operators, fn(op) {
    let pattern =
      Seq([
        Ref(first_rule),
        Many(Seq([Keyword(op.keyword), Ref(first_rule)])),
      ])
    Alternative(pattern: pattern, constructor: fn(values) {
      case values {
        [AstValue(first), ListValue(rest_values)] -> {
          fold_operators(first, rest_values, op.constructor)
        }
        _ -> panic as "left_assoc constructor: unexpected values"
      }
    })
  })
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
        ListValue([KeywordValue(_), AstValue(right)]) -> {
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
      Alternative(pattern: pattern, constructor: fn(values) {
        case values {
          [AstValue(left), KeywordValue(_), AstValue(right)] ->
            op.constructor(left, right)
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
  pattern: Pattern,
  constructor: fn(List(Value(a))) -> a,
) -> Alternative(a) {
  Alternative(pattern: pattern, constructor: constructor)
}

// ============================================================================
// PATTERN HELPERS
// ============================================================================

pub fn token_pattern(kind: String) -> Pattern {
  TokenKind(kind)
}

pub fn keyword_pattern(value: String) -> Pattern {
  Keyword(value)
}

pub fn ref(name: String) -> Pattern {
  Ref(name)
}

pub fn seq(patterns: List(Pattern)) -> Pattern {
  Seq(patterns)
}

pub fn choice(alts: List(Pattern)) -> Pattern {
  Choice(alts)
}

pub fn opt(pattern: Pattern) -> Pattern {
  Opt(pattern)
}

pub fn many(pattern: Pattern) -> Pattern {
  Many(pattern)
}

pub fn sep1(item: Pattern, sep: Pattern) -> Pattern {
  Sep1(item, sep)
}

pub fn parenthesized(rule_name: String) -> Pattern {
  seq([token_pattern("LParen"), ref(rule_name), token_pattern("RParen")])
}

// ============================================================================
// OPERATOR CONSTRUCTION
// ============================================================================

pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
) -> Operator(a) {
  Operator(
    keyword: keyword,
    constructor: constructor,
    precedence: precedence,
    associativity: Left,
    layout: Inline,
  )
}

pub fn op_with_layout(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
  layout: LayoutStyle,
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
  pattern: Pattern,
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value(a)), Int), Nil) {
  case pattern {
    TokenKind(kind) -> parse_token_kind(tokens, pos, kind)
    Keyword(value) -> parse_keyword(tokens, pos, value)
    Ref(rule_name) -> parse_ref(grammar, rule_name, tokens, pos)
    Seq(patterns) -> parse_seq(grammar, patterns, tokens, pos, [])
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
  patterns: List(Pattern),
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

fn parse_choice(
  grammar: Grammar(a),
  alts: List(Pattern),
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
  pattern: Pattern,
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
  pattern: Pattern,
  tokens: List(Token),
  pos: Int,
  values: List(Value(a)),
) -> Result(#(List(Value(a)), Int), Nil) {
  case parse_pattern(grammar, pattern, tokens, pos) {
    Ok(#(parsed, new_pos)) ->
      parse_many(grammar, pattern, tokens, new_pos, list.append(values, parsed))
    Error(_) -> Ok(#(values, pos))
  }
}

fn parse_sep1(
  grammar: Grammar(a),
  item: Pattern,
  sep: Pattern,
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
  item: Pattern,
  sep: Pattern,
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
// FORMATTER
// ============================================================================

pub fn format(grammar: Grammar(a), ast: a) -> String {
  let doc = format_ast(grammar, ast, -1)
  formatter.render(doc, 80)
}

fn format_ast(grammar: Grammar(a), ast: a, parent_prec: Int) -> Doc {
  case find_operator_for_ast(grammar, ast) {
    Some(op) -> format_by_operator(grammar, op, ast, parent_prec)
    None -> format_by_rules(grammar, ast, parent_prec)
  }
}

fn find_operator_for_ast(grammar: Grammar(a), ast: a) -> Option(Operator(a)) {
  // For now, return None - full implementation would need runtime type inspection
  None
}

fn format_by_operator(
  grammar: Grammar(a),
  op: Operator(a),
  ast: a,
  parent_prec: Int,
) -> Doc {
  // Would need deconstructor here - simplified for now
  formatter.text("<operator>")
}

fn format_by_rules(grammar: Grammar(a), ast: a, parent_prec: Int) -> Doc {
  // Would need to find rule and format - simplified for now
  formatter.text("<ast>")
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
