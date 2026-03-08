// ============================================================================
// GRAMMAR - Unified Grammar DSL with Automatic Parser/Formatter Generation
// ============================================================================
/// A declarative grammar system where:
/// - Grammar is the **single source of truth**
/// - Parser is automatically generated
/// - Formatter is automatically generated
/// - Precedence and associativity handled correctly
///
/// # Example
///
/// ```gleam
/// pub fn calc_grammar() -> Grammar(Expr) {
///   use g <- grammar.define
///
///   g
///   |> grammar.left_assoc("Expr", "Term", [
///     grammar.op("+", Add, 10),
///     grammar.op("-", Sub, 10),
///   ])
///   |> grammar.rule("Factor", [
///     grammar.alt("Number", fn(n) { Int(n) }),
///     grammar.alt(parens("Expr"), fn(e) { e }),
///   ])
/// }
///
/// let grammar = calc_grammar()
/// let result = grammar.parse(grammar, "1 + 2 * 3")
/// let source = grammar.format(grammar, result.ast)
/// ```
import syntax/formatter.{type Doc}
import syntax/lexer.{type Token}
import gleam/dict.{type Dict}
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result

// ============================================================================
// TYPES
// ============================================================================

/// Associativity of operators
pub type Associativity {
  Left
  Right
  NonAssoc
}

/// Layout style for formatting
pub type LayoutStyle {
  Inline
  BreakAfterOperator(indent: Int)
  BreakBeforeOperator(indent: Int)
  Block(open: String, close: String, indent: Int)
}

/// Pattern for matching input
pub type Pattern {
  /// Match a token by kind (e.g., "Number", "Ident")
  TokenKind(kind: String)
  /// Match a specific keyword value
  Keyword(value: String)
  /// Reference another rule
  Ref(rule: String)
  /// Sequence of patterns
  Seq(patterns: List(Pattern))
  /// Choice between alternatives
  Choice(alts: List(Pattern))
  /// Optional pattern
  Opt(pattern: Pattern)
  /// Zero or more repetitions
  Many(pattern: Pattern)
  /// One or more repetitions, separated
  Sep1(item: Pattern, sep: Pattern)
  /// Parenthesized expression (special handling for formatting)
  Parens(rule: String)
}

/// Alternative in a rule
pub type Alternative(a) {
  Alternative(
    pattern: Pattern,
    constructor: fn(List(Value)) -> a,
    /// Extract values from AST for formatting (reverse of constructor)
    deconstructor: fn(a) -> List(Value),
  )
}

/// Grammar rule
pub type Rule(a) {
  Rule(
    name: String,
    alternatives: List(Alternative(a)),
    precedence: Int,
  )
}

/// Operator for left/right/non-assoc rules
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,
    deconstructor: fn(a) -> #(a, a),
    precedence: Int,
    associativity: Associativity,
    layout: LayoutStyle,
  )
}

/// Unified grammar
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

/// Grammar builder (accumulates rules)
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

type ParseState =
  #(List(Token), Int)

type ParseResult(a) =
  Result(#(a, Int), Nil)

// ============================================================================
// GRAMMAR DEFINITION API
// ============================================================================

/// Start defining a grammar
pub fn define<A>(builder_fn: fn(GrammarBuilder(A)) -> GrammarBuilder(A)) -> Grammar(A) {
  let empty = GrammarBuilder(
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

/// Convert builder to final grammar
fn to_grammar<A>(builder: GrammarBuilder(A)) -> Grammar(A) {
  let rules_dict = list.fold(builder.rules, dict.new(), fn(acc, rule) {
    dict.insert(acc, rule.name, rule)
  })

  let operators_dict = list.fold(builder.operators, dict.new(), fn(acc, op) {
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

/// Set grammar name
pub fn name(builder: GrammarBuilder(a), name: String) -> GrammarBuilder(a) {
  GrammarBuilder(..builder, name: name)
}

/// Set start rule
pub fn start(builder: GrammarBuilder(a), rule: String) -> GrammarBuilder(a) {
  GrammarBuilder(..builder, start: rule)
}

/// Add token kind
pub fn token(builder: GrammarBuilder(a), kind: String) -> GrammarBuilder(a) {
  GrammarBuilder(..builder, tokens: [kind, ..builder.tokens])
}

/// Add keyword
pub fn keyword(builder: GrammarBuilder(a), kw: String) -> GrammarBuilder(a) {
  GrammarBuilder(..builder, keywords: [kw, ..builder.keywords])
}

// ============================================================================
// RULE DEFINITION
// ============================================================================

/// Add a basic rule with alternatives
pub fn rule<A>(
  builder: GrammarBuilder(A),
  name: String,
  alternatives: List(Alternative(A)),
) -> GrammarBuilder(A) {
  let rule = Rule(name: name, alternatives: alternatives, precedence: 0)
  GrammarBuilder(..builder, rules: [rule, ..builder.rules])
}

/// Add rule with explicit precedence
pub fn rule_with_precedence<A>(
  builder: GrammarBuilder(A),
  name: String,
  alternatives: List(Alternative(A)),
  precedence: Int,
) -> GrammarBuilder(A) {
  let rule = Rule(name: name, alternatives: alternatives, precedence: precedence)
  GrammarBuilder(..builder, rules: [rule, ..builder.rules])
}

/// Add left-associative operator rule
pub fn left_assoc<A>(
  builder: GrammarBuilder(A),
  name: String,
  first_rule: String,
  operators: List(Operator(A)),
  precedence: Int,
) -> GrammarBuilder(A) {
  // Create alternatives for the operator rule
  let op_alts = create_operator_alternatives(operators, first_rule, precedence)
  let first_alt = alt(ref(first_rule), fn(values) {
    case values {
      [first] -> first
      _ -> panic as "left_assoc: expected single value"
    }
  })

  let rule = Rule(
    name: name,
    alternatives: [first_alt, ..op_alts],
    precedence: precedence,
  )

  let builder = GrammarBuilder(..builder, rules: [rule, ..builder.rules])
  let builder = list.fold(operators, builder, fn(b, op) {
    GrammarBuilder(..b, operators: [op, ..b.operators])
  })
  builder
}

fn create_operator_alternatives<A>(
  operators: List(Operator(A)),
  first_rule: String,
  precedence: Int,
) -> List(Alternative(A)) {
  list.map(operators, fn(op) {
    // Pattern: first (op first)+
    // This parses: first op first op first ...
    // And folds left-to-right
    let pattern = Seq([
      Ref(first_rule),
      Many(Seq([
        Keyword(op.keyword),
        Ref(first_rule),
      ])),
    ])

    Alternative(
      pattern: pattern,
      constructor: fn(values) {
        case values {
          [first, rest_values] -> {
            fold_operators(first, rest_values, op.constructor)
          }
          _ -> panic as "left_assoc constructor: unexpected values"
        }
      },
      deconstructor: fn(ast) {
        // For formatting, we need to extract left and right operands
        // This is tricky for left-assoc - we store the operator info
        [ast]
      },
    )
  })
}

fn fold_operators<A>(
  first: A,
  rest_values: List(Value),
  apply: fn(A, A) -> A,
) -> A {
  case rest_values {
    [] -> first
    [op_right, ..more] -> {
      case op_right {
        [_, right] -> {
          let new_first = apply(first, right)
          fold_operators(new_first, more, apply)
        }
        _ -> first
      }
    }
  }
}

/// Add right-associative operator rule
pub fn right_assoc<A>(
  builder: GrammarBuilder(A),
  name: String,
  first_rule: String,
  operators: List(Operator(A)),
  precedence: Int,
) -> GrammarBuilder(A) {
  // Similar to left_assoc but builds right-associative AST
  let op_alts = list.map(operators, fn(op) {
    let pattern = Seq([
      Ref(first_rule),
      Keyword(op.keyword),
      Ref(name), // Recursive for right-assoc
    ])

    Alternative(
      pattern: pattern,
      constructor: fn(values) {
        case values {
          [left, _, right] -> op.constructor(left, right)
          _ -> panic as "right_assoc constructor: expected 3 values"
        }
      },
      deconstructor: op.deconstructor,
    )
  })

  let first_alt = alt(ref(first_rule), fn(values) {
    case values {
      [first] -> first
      _ -> panic as "right_assoc: expected single value"
    }
  })

  let rule = Rule(
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

/// Create an alternative
pub fn alt<A>(
  pattern: Pattern,
  constructor: fn(List(Value)) -> A,
) -> Alternative(A) {
  Alternative(
    pattern: pattern,
    constructor: constructor,
    deconstructor: fn(_) { [] }, // Default: no deconstruction
  )
}

/// Create alternative with deconstructor
pub fn alt_with_deconstructor<A>(
  pattern: Pattern,
  constructor: fn(List(Value)) -> A,
  deconstructor: fn(A) -> List(Value),
) -> Alternative(A) {
  Alternative(
    pattern: pattern,
    constructor: constructor,
    deconstructor: deconstructor,
  )
}

// ============================================================================
// PATTERN HELPERS
// ============================================================================

pub fn token(kind: String) -> Pattern {
  TokenKind(kind)
}

pub fn keyword(value: String) -> Pattern {
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

pub fn parens(rule_name: String) -> Pattern {
  Parens(rule_name)
}

/// Shorthand for parenthesized expression pattern
pub fn parenthesized(rule_name: String) -> Pattern {
  seq([
    token("LParen"),
    ref(rule_name),
    token("RParen"),
  ])
}

// ============================================================================
// OPERATOR CONSTRUCTION
// ============================================================================

/// Create operator with default settings
pub fn op<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  precedence: Int,
) -> Operator(A) {
  Operator(
    keyword: keyword,
    constructor: constructor,
    deconstructor: fn(ast) { panic as "Deconstructor not implemented" },
    precedence: precedence,
    associativity: Left,
    layout: Inline,
  )
}

/// Create operator with custom associativity
pub fn op_with_assoc<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  precedence: Int,
  associativity: Associativity,
) -> Operator(A) {
  Operator(
    keyword: keyword,
    constructor: constructor,
    deconstructor: fn(ast) { panic as "Deconstructor not implemented" },
    precedence: precedence,
    associativity: associativity,
    layout: Inline,
  )
}

/// Create operator with custom layout
pub fn op_with_layout<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  precedence: Int,
  layout: LayoutStyle,
) -> Operator(A) {
  Operator(
    keyword: keyword,
    constructor: constructor,
    deconstructor: fn(ast) { panic as "Deconstructor not implemented" },
    precedence: precedence,
    associativity: Left,
    layout: layout,
  )
}

/// Create operator with full customization
pub fn op_full<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  deconstructor: fn(A) -> #(A, A),
  precedence: Int,
  associativity: Associativity,
  layout: LayoutStyle,
) -> Operator(A) {
  Operator(
    keyword: keyword,
    constructor: constructor,
    deconstructor: deconstructor,
    precedence: precedence,
    associativity: associativity,
    layout: layout,
  )
}

// ============================================================================
// PARSER
// ============================================================================

pub type ParseError {
  ParseError(position: lexer.Position, expected: String, got: String)
}

pub type ParseResult(a) {
  ParseResult(ast: a, errors: List(ParseError))
}

/// Parse source using grammar
pub fn parse<A>(grammar: Grammar(A), source: String) -> ParseResult(A) {
  let tokens = lexer.tokenize(source)

  case dict.get(grammar.rules, grammar.start) {
    Ok(rule) -> {
      case parse_rule(grammar, rule, tokens, 0) {
        Ok(#(ast, _)) -> ParseResult(ast: ast, errors: [])
        Error(err) -> ParseResult(ast: panic as "Parse failed", errors: [err])
      }
    }
    Error(_) -> ParseResult(
      ast: panic as "No start rule",
      errors: [ParseError(
        position: lexer.Position(0, 1, 1),
        expected: "start rule",
        got: "none",
      )],
    )
  }
}

fn parse_rule<A>(
  grammar: Grammar(A),
  rule: Rule(A),
  tokens: List(Token),
  pos: Int,
) -> ParseResult(#(A, Int)) {
  // Try each alternative
  try_alternatives(grammar, rule.alternatives, tokens, pos)
}

fn try_alternatives<A>(
  grammar: Grammar(A),
  alternatives: List(Alternative(A)),
  tokens: List(Token),
  pos: Int,
) -> ParseResult(#(A, Int)) {
  case alternatives {
    [] -> Error(ParseError(
      position: get_token_pos(tokens, pos),
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

fn parse_pattern<A>(
  grammar: Grammar(A),
  pattern: Pattern,
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value), Int), Nil) {
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
) -> Result(#(List(Value), Int), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.kind == kind -> {
      Ok(#([[TokenValue(token)], pos + 1]))
    }
    _ -> Error(Nil)
  }
}

fn parse_keyword(
  tokens: List(Token),
  pos: Int,
  value: String,
) -> Result(#(List(Value), Int), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.value == value -> {
      Ok(#([[KeywordValue(token)], pos + 1]))
    }
    _ -> Error(Nil)
  }
}

fn parse_ref<A>(
  grammar: Grammar(A),
  rule_name: String,
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value), Int), Nil) {
  case dict.get(grammar.rules, rule_name) {
    Ok(rule) -> {
      case parse_rule(grammar, rule, tokens, pos) {
        Ok(#(ast, new_pos)) -> Ok(#([[AstValue(ast)], new_pos)])
        Error(_) -> Error(Nil)
      }
    }
    Error(_) -> Error(Nil)
  }
}

fn parse_seq<A>(
  grammar: Grammar(A),
  patterns: List(Pattern),
  tokens: List(Token),
  pos: Int,
  values: List(Value),
) -> Result(#(List(Value), Int), Nil) {
  case patterns {
    [] -> Ok(#(values, pos))
    [p, ..rest] -> {
      case parse_pattern(grammar, p, tokens, pos) {
        Ok(#(parsed, new_pos)) -> {
          let new_values = list.append(values, parsed)
          parse_seq(grammar, rest, tokens, new_pos, new_values)
        }
        Error(_) -> Error(Nil)
      }
    }
  }
}

fn parse_choice<A>(
  grammar: Grammar(A),
  alts: List(Pattern),
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value), Int), Nil) {
  case alts {
    [] -> Error(Nil)
    [alt, ..rest] -> {
      case parse_pattern(grammar, alt, tokens, pos) {
        Ok(result) -> result
        Error(_) -> parse_choice(grammar, rest, tokens, pos)
      }
    }
  }
}

fn parse_opt<A>(
  grammar: Grammar(A),
  pattern: Pattern,
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value), Int), Nil) {
  case parse_pattern(grammar, pattern, tokens, pos) {
    Ok(result) -> result
    Error(_) -> Ok(#([], pos))
  }
}

fn parse_many<A>(
  grammar: Grammar(A),
  pattern: Pattern,
  tokens: List(Token),
  pos: Int,
  values: List(Value),
) -> Result(#(List(Value), Int), Nil) {
  case parse_pattern(grammar, pattern, tokens, pos) {
    Ok(#(parsed, new_pos)) -> parse_many(grammar, pattern, tokens, new_pos, list.append(values, parsed))
    Error(_) -> Ok(#(values, pos))
  }
}

fn parse_sep1<A>(
  grammar: Grammar(A),
  item: Pattern,
  sep: Pattern,
  tokens: List(Token),
  pos: Int,
  values: List(Value),
) -> Result(#(List(Value), Int), Nil) {
  // Parse first item
  case parse_pattern(grammar, item, tokens, pos) {
    Ok(#(first, new_pos)) -> {
      parse_sep1_loop(grammar, item, sep, tokens, new_pos, list.append(values, first))
    }
    Error(_) -> Error(Nil)
  }
}

fn parse_sep1_loop<A>(
  grammar: Grammar(A),
  item: Pattern,
  sep: Pattern,
  tokens: List(Token),
  pos: Int,
  values: List(Value),
) -> Result(#(List(Value), Int), Nil) {
  // Try to parse separator + item
  case parse_pattern(grammar, sep, tokens, pos) {
    Ok(#(_, sep_pos)) -> {
      case parse_pattern(grammar, item, tokens, sep_pos) {
        Ok(#(parsed, new_pos)) -> {
          parse_sep1_loop(grammar, item, sep, tokens, new_pos, list.append(values, parsed))
        }
        Error(_) -> Ok(#(values, pos))
      }
    }
    Error(_) -> Ok(#(values, pos))
  }
}

fn parse_parens<A>(
  grammar: Grammar(A),
  rule_name: String,
  tokens: List(Token),
  pos: Int,
) -> Result(#(List(Value), Int), Nil) {
  // Parse LParen expr RParen
  case parse_pattern(grammar, token("LParen"), tokens, pos) {
    Ok(#(_, lparen_pos)) -> {
      case parse_ref(grammar, rule_name, tokens, lparen_pos) {
        Ok(#(expr_values, expr_pos)) -> {
          case parse_pattern(grammar, token("RParen"), tokens, expr_pos) {
            Ok(#(_, rparen_pos)) -> {
              // Wrap in ParensValue for special formatting
              Ok(#([[ParensValue(expr_values)], rparen_pos]))
            }
            Error(_) -> Error(Nil)
          }
        }
        Error(_) -> Error(Nil)
      }
    }
    Error(_) -> Error(Nil)
  }
}

// ============================================================================
// VALUE TYPES (for constructor arguments)
// ============================================================================

pub type Value {
  TokenValue(Token)
  KeywordValue(Token)
  AstValue(a)
  ParensValue(List(Value))
  ListValue(List(Value))
}

// ============================================================================
// HELPERS
// ============================================================================

fn get_token(tokens: List(Token), pos: Int) -> Result(Token, Nil) {
  case list.at(tokens, pos) {
    Ok(token) -> Ok(token)
    Error(_) -> Error(Nil)
  }
}

fn get_token_pos(tokens: List(Token), pos: Int) -> lexer.Position {
  case get_token(tokens, pos) {
    Ok(token) -> token.start
    Error(_) -> lexer.Position(pos, 1, 1)
  }
}

// ============================================================================
// FORMATTER
// ============================================================================

/// Format AST using grammar
pub fn format<A>(grammar: Grammar(A), ast: A) -> String {
  let doc = format_ast(grammar, ast, -1)
  formatter.render(doc, 80)
}

fn format_ast<A>(grammar: Grammar(A), ast: A, parent_prec: Int) -> Doc {
  // Try to find operator for this AST
  case find_operator_for_ast(grammar, ast) {
    Some(op) -> format_by_operator(grammar, op, ast, parent_prec)
    None => format_by_rules(grammar, ast, parent_prec)
  }
}

fn find_operator_for_ast<A>(grammar: Grammar(A), ast: A) -> Option(Operator(A)) {
  // This requires runtime type inspection which Gleam doesn't support
  // For now, we return None and fall back to rule-based formatting
  // In a full implementation, we'd store operator tags in the AST
  None
}

fn format_by_operator<A>(
  grammar: Grammar(A),
  op: Operator(A),
  ast: A,
  parent_prec: Int,
) -> Doc {
  let #(left, right) = op.deconstructor(ast)
  let left_doc = format_ast(grammar, left, op.precedence)
  let right_doc = format_ast(grammar, right, op.precedence + 1)

  formatter.format_binop(
    left_doc,
    right_doc,
    op.keyword,
    op.precedence,
    parent_prec,
    op.layout,
  )
}

fn format_by_rules<A>(grammar: Grammar(A), ast: A, parent_prec: Int) -> Doc {
  // Find the rule that created this AST and use its format template
  // For now, return a placeholder
  formatter.text("<ast>")
}
