/// Grammar DSL - Minimal parser combinators for declarative grammar definition
import gleam/list
import gleam/string
import syntax/lexer
import syntax/span

// Pattern types

pub type Pattern(a) {
  Ref(String)
  TokenKind(String)
  Keyword(String)
  Operator(String)
  Seq(List(Pattern(a)))
  Opt(Pattern(a))
  Many(Pattern(a))
  Choice(List(Pattern(a)))
}

pub type Alternative(a) {
  Alternative(pattern: Pattern(a), constructor: fn(List(a)) -> a)
}

pub type Rule(a) {
  Rule(name: String, alternatives: List(Alternative(a)), precedence: Int)
}

pub type Operator(a) {
  Prefix(precedence: Int, symbol: String, constructor: fn(a) -> a)
  Postfix(precedence: Int, symbol: String, constructor: fn(a) -> a)
  Infix(
    precedence: Int,
    infix_op: String,
    constructor: fn(a, a) -> a,
  )
}

pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: List(Rule(a)),
    keywords: List(String),
    operators: List(#(String, Operator(a))),
  )
}

// Helper constructors

pub fn rule(name: String, alt: Alternative(a)) -> Rule(a) {
  Rule(name: name, alternatives: [alt], precedence: 0)
}

pub fn rule_multi(name: String, alts: List(Alternative(a))) -> Rule(a) {
  Rule(name: name, alternatives: alts, precedence: 0)
}

pub fn tok(kind: String) -> Pattern(a) { TokenKind(kind) }
pub fn kw(value: String) -> Pattern(a) { Keyword(value) }
pub fn op(symbol: String) -> Pattern(a) { Operator(symbol) }
pub fn ref_name(name: String) -> Pattern(a) { Ref(name) }
pub fn seq(patterns: List(Pattern(a))) -> Pattern(a) { Seq(patterns) }
pub fn opt(pattern: Pattern(a)) -> Pattern(a) { Opt(pattern) }
pub fn many(pattern: Pattern(a)) -> Pattern(a) { Many(pattern) }
pub fn choice(alternatives: List(Pattern(a))) -> Pattern(a) { Choice(alternatives) }
pub fn alt(pattern: Pattern(a), constructor: fn(List(a)) -> a) -> Alternative(a) {
  Alternative(pattern: pattern, constructor: constructor)
}

pub fn make_grammar(
  name: String,
  start: String,
  rules: List(Rule(a)),
  keywords: List(String),
  operators: List(#(String, Operator(a))),
) -> Grammar(a) {
  Grammar(
    name: name,
    start: start,
    rules: rules,
    keywords: keywords,
    operators: operators,
  )
}

// Parse result

pub type ParseError {
  ParseError(span: span.Span, expected: String, got: String, context: String)
}

pub type ParseResult(a) {
  ParseResult(ast: a, errors: List(ParseError))
}

// Parser state

type State(a) {
  State(remaining: List(lexer.Token), errors: List(ParseError), values: List(a))
}

// Public parse function

pub fn parse(grammar: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(source, grammar.name)
  let rules_dict = list.map(grammar.rules, fn(r) { #(r.name, r) })
  
  let initial = State(remaining: tokens, errors: [], values: [])
  case parse_rule(grammar.start, initial, rules_dict) {
    State(values: [val], errors: errs, ..) -> ParseResult(ast: val, errors: errs)
    State(values: values, errors: errs, ..) -> ParseResult(ast: panic, errors: errs)
  }
}

fn parse_rule(rule_name: String, state: State(a), rules_dict: List(#(String, Rule(a)))) -> State(a) {
  case find_rule(rules_dict, rule_name) {
    Rule(name: _, alternatives: alts, precedence: _) ->
      parse_alternatives(alts, state, rules_dict)
  }
}

fn find_rule(rules_dict: List(#(String, Rule(a))), name: String) -> Rule(a) {
  case list.find(rules_dict, fn(pair) { pair.0 == name }) {
    Ok(#(_, rule)) -> rule
    Error(_) -> Rule(name: name, alternatives: [], precedence: 0)
  }
}

fn parse_alternatives(alternatives: List(Alternative(a)), state: State(a), rules_dict: List(#(String, Rule(a)))) -> State(a) {
  case alternatives {
    [] -> state
    [first, ..rest] -> {
      case parse_alternative(first, state, rules_dict) {
        State(values: [_], ..) as success -> success
        State(values: _, ..) as failed -> parse_alternatives(rest, failed, rules_dict)
      }
    }
  }
}

fn parse_alternative(alt: Alternative(a), state: State(a), rules_dict: List(#(String, Rule(a)))) -> State(a) {
  let State(remaining: tokens, errors: errs, values: acc) = state
  case parse_pattern(alt.pattern, State(..state, values: []), rules_dict) {
    State(values: vals, errors: new_errs, remaining: _) ->
      State(remaining: tokens, errors: list.append(errs, new_errs), values: [alt.constructor(vals)])
  }
}

fn parse_pattern(pattern: Pattern(a), state: State(a), rules_dict: List(#(String, Rule(a)))) -> State(a) {
  let State(remaining: tokens, errors: errs, values: acc) = state
  case pattern {
    Ref(rule_name) ->
      parse_rule(rule_name, State(..state, values: []), rules_dict)
    TokenKind(kind) ->
      case tokens {
        [lexer.Token(kind: k, value: _, span: _), ..rest] if k == kind ->
          State(remaining: rest, errors: errs, values: acc)
        _ -> State(remaining: tokens, errors: list.append(error_parse(kind, tokens), errs), values: acc)
      }
    Keyword(value) ->
      case tokens {
        [lexer.Token(kind: "Keyword", value: v, span: _), ..rest] if v == value ->
          State(remaining: rest, errors: errs, values: acc)
        _ -> State(remaining: tokens, errors: list.append(error_parse(value, tokens), errs), values: acc)
      }
    Operator(symbol) ->
      case tokens {
        [lexer.Token(kind: k, value: v, span: _), ..rest] if k == "Operator" && v == symbol ->
          State(remaining: rest, errors: errs, values: acc)
        _ -> State(remaining: tokens, errors: list.append(error_parse(symbol, tokens), errs), values: acc)
      }
    Seq(patterns) ->
      parse_seq(patterns, State(..state, values: []), rules_dict)
    Opt(pattern) ->
      case parse_pattern(pattern, State(..state, values: []), rules_dict) {
        State(values: [_], ..) as matched -> matched
        State(values: _, ..) -> state
      }
    Many(pattern) ->
      parse_many(pattern, State(..state, values: []), rules_dict)
    Choice(alternatives) ->
      parse_alternatives(list.map(alternatives, fn(p) { alt(p, single_value) }), state, rules_dict)
  }
}


fn single_value(xs: List(a)) -> a {
  case xs {
    [x] -> x
    _ -> panic as "choice expected exactly one value"
  }
}
fn parse_seq(patterns: List(Pattern(a)), state: State(a), rules_dict: List(#(String, Rule(a)))) -> State(a) {
  case patterns {
    [] -> state
    [first, ..rest] ->
      case parse_pattern(first, state, rules_dict) {
        State(values: [val], errors: errs, remaining: remaining) ->
          parse_seq(rest, State(remaining: remaining, errors: errs, values: []), rules_dict)
        s -> s
      }
  }
}

fn parse_many(pattern: Pattern(a), state: State(a), rules_dict: List(#(String, Rule(a)))) -> State(a) {
  case parse_pattern(pattern, state, rules_dict) {
    State(values: [val], errors: errs, remaining: remaining) ->
      parse_many(pattern, State(remaining: remaining, errors: errs, values: []), rules_dict)
    s -> s
  }
}

fn error_parse(expected: String, tokens: List(lexer.Token)) -> List(ParseError) {
  let got = case tokens {
    [] -> "end of input"
    [lexer.Token(kind: k, value: v, span: _), ..] -> "token: " <> k <> " (" <> v <> ")"
  }
  [ParseError(span: span.dummy(), expected: expected, got: got, context: "")]
}

// ============================================================================
// FORMATTER - Simple document algebra (merged from formatter.gleam)
// As per simplified design: formatting is simple, no LayoutHint needed
// ============================================================================

/// Document type for formatting
pub type Doc {
  Empty
  Text(String)
  Line                 // Breakable space (" " when flat, nothing when broken)
  HardLine             // Unbreakable newline
  Group(Doc)           // Optimize: flatten if fits on one line
  Nest(Int, Doc)       // Indent by N spaces
  Concat(List(Doc))
}

/// Create an empty document
pub fn empty() -> Doc {
  Empty
}

/// Create a text document
pub fn text(s: String) -> Doc {
  case s == "" {
    True -> Empty
    False -> Text(s)
  }
}

/// Create a line break
pub fn line() -> Doc {
  Line
}

/// Create a space
pub fn space() -> Doc {
  Text(" ")
}

/// Create a hard line break
pub fn hardline() -> Doc {
  HardLine
}

/// Concatenate documents
pub fn concat(docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [d] -> d
    _ -> Concat(docs)
  }
}

/// Append two documents
pub fn append(d1: Doc, d2: Doc) -> Doc {
  concat([d1, d2])
}

/// Group a document for optimization
pub fn group(doc: Doc) -> Doc {
  Group(doc)
}

/// Nest (indent) a document by N spaces
pub fn nest(n: Int, doc: Doc) -> Doc {
  Nest(n, doc)
}

/// Join documents with a separator (space when flat, comma+newline when broken)
pub fn join(sep: Doc, docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [first] -> first
    [first, ..rest] -> {
      list.fold(rest, first, fn(acc, doc) {
        concat([acc, sep, doc])
      })
    }
  }
}

/// Space-separated list
pub fn space_sep(docs: List(Doc)) -> Doc {
  join(Text(" "), docs)
}

/// Comma-separated list with line breaks
pub fn comma_sep(docs: List(Doc)) -> Doc {
  join(Text(","), docs)
}

/// Wrap document in parentheses
pub fn parens(doc: Doc) -> Doc {
  concat([Text("("), doc, Text(")")])
}

/// Wrap document in braces
pub fn braces(doc: Doc) -> Doc {
  concat([Text("{"), doc, Text("}")])
}

/// Wrap document in brackets
pub fn brackets(doc: Doc) -> Doc {
  concat([Text("["), doc, Text("]")])
}

/// Format a document to a string (flat layout)
pub fn format_flat(doc: Doc) -> String {
  case doc {
    Empty -> ""
    Text(s) -> s
    Line -> " "
    HardLine -> "\n"
    Group(inner) -> format_flat(inner)
    Nest(n, inner) -> format_flat(inner)  // Nesting ignored in flat layout
    Concat(docs) -> string.join(list.map(docs, format_flat), "")
  }
}

/// Format a document to a string (with simple layout)
pub fn format_doc(doc: Doc, width: Int) -> String {
  format_flat(doc)
}
