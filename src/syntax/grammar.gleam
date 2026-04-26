/// Parser Combinator DSL
///
/// Provides a minimal set of combinators for building recursive-descent
/// parsers over token streams. The key design insight is that the parser
/// uses `Either` as an intermediate type: terminals produce `Left(string)`
/// values and non-terminals produce `Right(ast_node)` values. This allows
/// all pattern combinators to work uniformly.
///
/// # Combinators
///
///   - `tok` — match a specific token kind (e.g., "Name", "Integer")
///   - `kw` — match a keyword (a Name token with a specific value)
///   - `op` — match a specific operator symbol (e.g., "+", "->")
///   - `ref` — reference another named rule in the grammar
///   - `seq` — sequence of parsers (all must match)
///   - `opt` — optional parser (always succeeds)
///   - `many` — zero or more of a parser
///   - `choice` — try alternatives in order (first match wins)
///   - `sep_by` — items separated by separator (zero or more)
///   - `parens` — parse `( inner_rule )`
///
/// # Example
///
/// ```gleam
/// import syntax/grammar.{Grammar, Rule, Alternative, tok, kw, op, ref, seq, opt, many, choice}
///
/// // Using Either to represent parsed values:
/// // Left(string) = terminal value (token/keyword/operator)
/// // Right(ast_node) = non-terminal value (parsed rule)
/// import gleam/option.{Some}
///
/// let grammar: Grammar(MyAst) = Grammar(
///   name: "Expr",
///   start: "Expr",
///   rules: [
///     Rule(
///       name: "Expr",
///       alternatives: [
///         Alternative(
///           pattern: seq([
///             ref("Expr"),      // Right(ast)
///             op("+"),           // Left("+")
///             ref("Expr"),      // Right(ast)
///           ]),
///           constructor: fn(values) {
///             // Extract Right values, build BinOp
///             // values: [ #(Right(node1), span), #(Left("+"), span), #(Right(node2), span) ]
///             BinOp(values.0.0, values.2.0)
///           },
///         ),
///         Alternative(
///           pattern: ref("Name"),
///           constructor: fn(values) { Var(values.0.0) },
///         ),
///       ],
///       precedence: 0,
///     ),
///   ],
///   keywords: ["fn", "let"],
///   operators: [],
/// )
/// ```

import gleam/list
import gleam/int
import syntax/span.{Span, type Span, empty}
import syntax/base_lexer.{type Token}

// ============================================================================
// PARSE RESULT AND ERRORS
// ============================================================================

/// Result of parsing — contains the parsed AST and any errors encountered.
///
/// Even on error, `ast` contains a partial or error AST so that the
/// compiler can continue processing and report all errors at once.
pub type ParseResult(a) {
  ParseResult(ast: a, errors: List(ParseError))
}

/// A parse error with source location and context.
pub type ParseError {
  ParseError(
    span: Span,
    expected: String,
    got: String,
    context: String,
  )
}

// ============================================================================
// GRAMMAR STRUCTURE
// ============================================================================

/// A complete grammar definition.
///
/// `a` is the AST type produced by this grammar.
/// The intermediate type for pattern matching is `Either(String, a)`,
/// where `Left(string)` represents a terminal (token/keyword/operator)
/// and `Right(node)` represents a non-terminal (parsed rule).
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: List(Rule(a)),
    keywords: List(String),
    operators: List(#(String, Operator(a))),
  )
}

/// A rule in the grammar.
///
/// A rule defines alternatives for parsing. Rules with `precedence > 0`
/// are operator rules and get special handling for precedence/associativity.
pub type Rule(a) {
  Rule(
    name: String,
    alternatives: List(Alternative(a)),
    precedence: Int,
  )
}

/// An alternative in a rule.
///
/// Each alternative has a pattern to match and a constructor to build
/// the AST node from the parsed values.
///
/// The `constructor` receives a list of `(either, span)` tuples — one for
/// each item in the pattern. Terminals produce `Left(string)` values,
/// non-terminals produce `Right(ast_node)` values.
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(#(Either(String, a), Span))) -> a,
  )
}

/// Intermediate value type for pattern parsing.
///
/// `Left(string)` = terminal value (from tok, kw, op)
/// `Right(node)` = non-terminal value (from ref — a parsed AST node)
///
/// This type allows all pattern combinators to work uniformly,
/// since every pattern can return an `Either(String, a)`.
pub type Either(left, right) {
  Left(value: left)
  Right(value: right)
}

// ============================================================================
// PATTERN COMBINATORS
// ============================================================================

/// Patterns that can be composed to form complete parsers.
///
/// Each pattern produces `Either(String, a)`:
/// - Terminals (Tok, Kw, Op) produce `Left(string)` values
/// - Ref produces `Right(ast_node)` values (the parsed rule's result)
/// - Combinators (Seq, Opt, Many, Choice) compose these uniformly
pub type Pattern(a) {
  Tok(String)                                         // Match a specific token kind
  Kw(String)                                          // Match a keyword by name
  Op(String)                                          // Match an operator symbol
  Ref(String)                                         // Reference another rule by name
  Seq(List(Pattern(a)))                               // Sequence of patterns
  Opt(Pattern(a))                                     // Optional pattern
  Many(Pattern(a))                                    // Zero or more of a pattern
  Choice(List(Pattern(a)))                            // Try alternatives in order
  SepBy(Pattern(a), Pattern(a))                       // Items separated by separator
  Parens(String)                                      // Parse: Lparens Rule Rparens
  Delimited(Pattern(a), Pattern(a), Pattern(a), Pattern(a)) // open items(sep item)* close
}

/// Operator definition for precedence handling.
pub type Operator(a) {
  Infix(
    Int,                         // Precedence (higher = binds tighter)
    Bool,                        // True = right-associative, False = left-associative
    String,                      // Operator symbol
    fn(a, a) -> a,               // Constructor combining left and right
  )
}

// ============================================================================
// PUBLIC API — CONSTRUCTING PATTERNS
// ============================================================================

/// Create a "tok" pattern for a specific token kind.
///
/// Matches a token whose `kind` field equals the given string.
/// Produces `Left(token_value)` on success.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar.{tok}
///
/// let name_pat = tok("Name")
/// ```
pub fn tok(kind: String) -> Pattern(a) {
  Tok(kind)
}

/// Create a "kw" pattern for a keyword.
///
/// Matches a Name token whose `value` equals the given keyword string.
/// Produces `Left(token_value)` on success.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar.{kw}
///
/// let let_kw = kw("let")
/// ```
pub fn kw(keyword: String) -> Pattern(a) {
  Kw(keyword)
}

/// Create an "op" pattern for an operator symbol.
///
/// Matches an Op token whose `value` equals the given symbol.
/// Produces `Left(token_value)` on success.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar.{op}
///
/// let add_op = op("+")
/// ```
pub fn op(symbol: String) -> Pattern(a) {
  Op(symbol)
}

/// Create a "ref" pattern for a rule reference.
///
/// References another named rule in the grammar. The string is the
/// rule name as defined in `Grammar.rules`.
/// Produces `Right(parsed_node)` on success.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar.{ref}
///
/// let expr_ref = ref("Expr")
/// ```
pub fn ref(rule_name: String) -> Pattern(a) {
  Ref(rule_name)
}

/// Create a "seq" pattern — sequence of sub-patterns.
///
/// All sub-patterns must succeed in order. The results are collected
/// into a single list in left-to-right order.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar::{seq, kw, ref}
///
/// let let_expr = seq([kw("let"), ref("Name"), kw("="), ref("Expr")])
/// ```
pub fn seq(patterns: List(Pattern(a))) -> Pattern(a) {
  Seq(patterns)
}

/// Create an "opt" pattern — optional sub-pattern.
///
/// Always succeeds. Returns parsed values if the pattern matches,
/// or an empty list if it doesn't.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar::{opt, kw}
///
/// let opt_comma = opt(kw(","))
/// ```
pub fn opt(pattern: Pattern(a)) -> Pattern(a) {
  Opt(pattern)
}

/// Create a "many" pattern — zero or more occurrences.
///
/// Matches the sub-pattern as many times as possible.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar::{many, kw}
///
/// let comma_names = many(seq([kw(","), ref("Name")]))
/// ```
pub fn many(pattern: Pattern(a)) -> Pattern(a) {
  Many(pattern)
}

/// Create a "choice" pattern — try alternatives in order.
///
/// Returns the first matching alternative. If none match, fails.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar::{choice, kw, tok}
///
/// let opt_int_or_name = choice([kw("int"), tok("Name")])
/// ```
pub fn choice(patterns: List(Pattern(a))) -> Pattern(a) {
  Choice(patterns)
}

/// Create a "sep_by" pattern — items separated by a separator.
///
/// Matches zero or more items separated by the separator pattern.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar::{sep_by, kw, tok}
///
/// let comma_separated = sep_by(ref("Expr"), kw(","))
/// ```
pub fn sep_by(item: Pattern(a), sep: Pattern(a)) -> Pattern(a) {
  SepBy(item, sep)
}

/// Create a "parens" pattern — parenthesized rule.
///
/// Matches `( Rule_name )`.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar.{parens}
///
/// let paren_expr = parens("Expr")
/// ```
pub fn parens(rule_name: String) -> Pattern(a) {
  Parens(rule_name)
}

/// Create a delimited pattern: `open (item sep item)* close`.
///
/// Matches a list of items separated by a separator, enclosed by
/// open/close delimiters.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar.{delimited, tok, kw}
///
/// let parens_comma_exprs = delimited(
///   tok("("),
///   ref("Expr"),
///   kw(","),
///   tok(")"),
/// )
/// ```
pub fn delimited(open: Pattern(a), item: Pattern(a), sep: Pattern(a), close: Pattern(a)) -> Pattern(a) {
  Delimited(open, item, sep, close)
}

// ============================================================================
// PUBLIC API — PARSING
// ============================================================================

/// Parse a grammar definition from a token list.
///
/// Returns a `ParseResult` containing the parsed AST (or error node)
/// and all parse errors encountered.
///
/// The `error_node` is used when the entire parse fails to produce
/// any AST node. The parser attempts to parse the `start` rule at
/// position 0 and consumes tokens until EOF.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar.{parse}
/// import syntax/lexer.{tokenize}
///
/// let tokens = tokenize("hello world")
/// let result = parse(grammar, tokens, "error_node")
/// ```
/// Parse a grammar definition from a token list.
///
/// Returns a `ParseResult` containing the parsed AST node and all parse
/// errors encountered. On success, the AST node is the result of applying
/// the rule's constructor to the parsed values. On failure, `error_node`
/// is returned as a fallback and all errors are accumulated.
///
/// The `error_node` is used when the entire parse fails to produce
/// any AST node. The parser attempts to parse the `start` rule at
/// position 0.
///
/// # Example
///
/// ```gleam
/// import syntax/grammar.{parse}
/// import syntax/lexer.{tokenize}
///
/// let tokens = tokenize("hello world")
/// let result = parse(grammar, tokens, "error_node")
/// ```
pub fn parse(grammar: Grammar(a), tokens: List(Token), error_node: a) -> ParseResult(a) {
  let errors = []
  case try_parse_rule(grammar, grammar.start, tokens, 0, errors) {
    Ok(#(values, _final_pos, new_errors)) -> {
      // Extract the constructed AST node from the first Right value.
      // The constructor already built the AST node in try_parse_alternative.
      let ast = case list.first(values) {
        Ok(#(Right(node), _span)) -> node
        _ -> error_node
      }
      ParseResult(ast: ast, errors: new_errors)
    }
    Error(_) -> ParseResult(ast: error_node, errors: errors)
  }
}

// ============================================================================
// PARSER IMPLEMENTATION
// ============================================================================

/// Parse a named rule from the grammar.
///
/// Returns `(either, span)` tuples on success, or an error string.
fn try_parse_rule(grammar: Grammar(a), rule_name: String, tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case find_rule(grammar, rule_name) {
    Error(msg) -> Error(msg)
    Ok(rule) -> try_parse_alternatives(grammar, rule.alternatives, tokens, pos, errors)
  }
}

/// Try all alternatives for a rule, returning the first success.
fn try_parse_alternatives(grammar: Grammar(a), alternatives: List(Alternative(a)), tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case alternatives {
    [] -> Error("rule has no alternatives")
    [alt, ..rest] -> {
      case try_parse_alternative(grammar, alt, tokens, pos, errors) {
        Ok(result) -> Ok(result)
        Error(_) -> try_parse_alternatives(grammar, rest, tokens, pos, errors)
      }
    }
  }
}

/// Try parsing a single alternative.
fn try_parse_alternative(grammar: Grammar(a), alternative: Alternative(a), tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case apply_pattern(grammar, alternative.pattern, tokens, pos, errors) {
    Ok(#(values, new_pos, new_errors)) -> {
      // The constructor builds the AST node from the values
      let constructed = alternative.constructor(values)
      // Return the constructed node as Right in the result list
      // along with a span covering the parsed range
      let span = span_cover(values)
      Ok(#([ #(Right(constructed), span) ], new_pos, new_errors))
    }
    Error(msg) -> Error(msg)
  }
}

/// Apply a pattern to the token stream starting at position `pos`.
///
/// Returns `(either, span)` tuples on success, or an error string.
/// Terminals produce `Left(string)` values, refs produce `Right(ast_node)` values.
fn apply_pattern(grammar: Grammar(a), pattern: Pattern(a), tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case pattern {
    Tok(kind) -> apply_tok(kind, tokens, pos, errors)
    Kw(keyword) -> apply_kw(keyword, tokens, pos, errors)
    Op(symbol) -> apply_op(symbol, tokens, pos, errors)
    Ref(rule_name) -> try_parse_rule(grammar, rule_name, tokens, pos, errors)
    Seq(pats) -> apply_seq(grammar, pats, tokens, pos, errors, [])
    Opt(pat) -> apply_opt(grammar, pat, tokens, pos, errors)
    Many(pat) -> apply_many(grammar, pat, tokens, pos, errors, [])
    Choice(alts) -> apply_choice(grammar, alts, tokens, pos, errors)
    SepBy(item, sep) -> apply_sep_by(grammar, item, sep, tokens, pos, errors, [])
    Parens(inner) -> apply_parens(grammar, inner, tokens, pos, errors)
    Delimited(open_p, item_p, sep_p, close_p) -> apply_delimited(grammar, open_p, item_p, sep_p, close_p, tokens, pos, errors)
  }
}

// --- Terminal Parsers ---

fn apply_tok(kind: String, tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case peek_token(tokens, pos) {
    Error(_) -> Error("expected token '" <> kind <> "'")
    Ok(token) -> case token.kind == kind || {
      // Also match punctuation tokens by value: Tok("(") matches Punct "(" 
      token.kind == "Punct" && token.value == kind
    } {
      True -> Ok(#([ #(Left(token.value), token.span) ], pos + 1, errors))
      False -> Error("expected token '" <> kind <> "'")
    }
  }
}

fn apply_kw(keyword: String, tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case peek_token(tokens, pos) {
    Error(_) -> Error("expected keyword '" <> keyword <> "'")
    Ok(token) -> case token.kind == "Name" && token.value == keyword {
      True -> Ok(#([ #(Left(token.value), token.span) ], pos + 1, errors))
      False -> Error("expected keyword '" <> keyword <> "'")
    }
  }
}

fn apply_op(symbol: String, tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case peek_token(tokens, pos) {
    Error(_) -> Error("expected operator '" <> symbol <> "'")
    Ok(token) -> case token.kind == "Op" && token.value == symbol {
      True -> Ok(#([ #(Left(token.value), token.span) ], pos + 1, errors))
      False -> Error("expected operator '" <> symbol <> "'")
    }
  }
}

// --- Combinator Parsers ---

fn apply_seq(grammar: Grammar(a), patterns: List(Pattern(a)), tokens: List(Token), pos: Int, errors: List(ParseError), acc: List(#(Either(String, a), Span))) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case patterns {
    [] -> Ok(#(list.reverse(acc), pos, errors))
    [pat, ..rest] -> {
      case apply_pattern(grammar, pat, tokens, pos, errors) {
        Ok(#(values, new_pos, new_errors)) -> {
          apply_seq(grammar, rest, tokens, new_pos, new_errors, list.append(values, acc))
        }
        Error(msg) -> Error(msg)
      }
    }
  }
}

fn apply_opt(grammar: Grammar(a), pattern: Pattern(a), tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case apply_pattern(grammar, pattern, tokens, pos, errors) {
    Ok(result) -> Ok(result)
    Error(_) -> Ok(#([], pos, errors))
  }
}

fn apply_many(grammar: Grammar(a), pattern: Pattern(a), tokens: List(Token), pos: Int, errors: List(ParseError), acc: List(#(Either(String, a), Span))) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case apply_pattern(grammar, pattern, tokens, pos, errors) {
    Ok(#(values, new_pos, new_errors)) -> {
      apply_many(grammar, pattern, tokens, new_pos, new_errors, list.append(values, acc))
    }
    Error(_) -> Ok(#(list.reverse(acc), pos, errors))
  }
}

fn apply_choice(grammar: Grammar(a), patterns: List(Pattern(a)), tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case patterns {
    [] -> Error("choice: no alternatives")
    [pat, ..rest] -> {
      case apply_pattern(grammar, pat, tokens, pos, errors) {
        Ok(result) -> Ok(result)
        Error(_) -> apply_choice(grammar, rest, tokens, pos, errors)
      }
    }
  }
}

fn apply_sep_by(grammar: Grammar(a), item: Pattern(a), sep: Pattern(a), tokens: List(Token), pos: Int, errors: List(ParseError), acc: List(#(Either(String, a), Span))) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case apply_pattern(grammar, item, tokens, pos, errors) {
    Ok(#(first, new_pos, new_errors)) -> {
      apply_sep_by_rest(grammar, item, sep, tokens, new_pos, new_errors, first)
    }
    Error(_) -> Ok(#(list.reverse(acc), pos, errors))
  }
}

fn apply_sep_by_rest(grammar: Grammar(a), item: Pattern(a), sep: Pattern(a), tokens: List(Token), pos: Int, errors: List(ParseError), acc: List(#(Either(String, a), Span))) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case apply_pattern(grammar, sep, tokens, pos, errors) {
    Ok(#(_, sep_pos, new_errors)) -> {
      case apply_pattern(grammar, item, tokens, sep_pos, new_errors) {
        Ok(#(val, next_pos, next_errors)) -> {
          apply_sep_by_rest(grammar, item, sep, tokens, next_pos, next_errors, list.append(val, acc))
        }
        Error(_) -> Ok(#(list.reverse(acc), pos, errors))
      }
    }
    Error(_) -> Ok(#(list.reverse(acc), pos, errors))
  }
}

fn apply_parens(grammar: Grammar(a), inner_name: String, tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  // ( Rule_name )
  let parens_pattern = Seq([Tok("("), Ref(inner_name), Tok(")")])
  apply_pattern(grammar, parens_pattern, tokens, pos, errors)
}

fn apply_delimited(grammar: Grammar(a), open_p: Pattern(a), item_p: Pattern(a), sep_p: Pattern(a), close_p: Pattern(a), tokens: List(Token), pos: Int, errors: List(ParseError)) -> Result(#(List(#(Either(String, a), Span)), Int, List(ParseError)), String) {
  case apply_pattern(grammar, open_p, tokens, pos, errors) {
    Ok(#(_, new_pos, new_errors)) -> {
      // Parse: item (sep item)* — requires at least one item, then zero or more (sep, item) pairs
      let repeated = Seq([item_p, Many(Seq([sep_p, item_p]))])
      case apply_pattern(grammar, repeated, tokens, new_pos, new_errors) {
        Ok(#(values, close_pos, close_errors)) -> {
          case apply_pattern(grammar, close_p, tokens, close_pos, close_errors) {
            Ok(#(_, final_pos, final_errors)) -> Ok(#(values, final_pos, final_errors))
            Error(msg) -> Error(msg)
          }
        }
        Error(msg) -> Error(msg)
      }
    }
    Error(msg) -> Error(msg)
  }
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Find a rule by name in the grammar.
fn find_rule(grammar: Grammar(a), name: String) -> Result(Rule(a), String) {
  find_rule_loop(grammar.rules, name)
}

fn find_rule_loop(rules: List(Rule(a)), name: String) -> Result(Rule(a), String) {
  case rules {
    [] -> Error("unknown rule '" <> name <> "'")
    [rule, ..rest] -> case rule.name == name {
      True -> Ok(rule)
      False -> find_rule_loop(rest, name)
    }
  }
}

/// Get the first non-EOF, non-comment token at position.
fn peek_token(tokens: List(Token), pos: Int) -> Result(Token, String) {
  case list.drop(tokens, pos) {
    [] -> Error("EOF")
    [token, .._] -> {
      case token.kind == "Eof" || token.kind == "Comment" {
        True -> Error("EOF")
        False -> Ok(token)
      }
    }
  }
}

/// Build a span covering the range of parsed values.
fn span_cover(values: List(#(Either(String, a), Span))) -> Span {
  case values {
    [] -> empty("", 1, 1)
    [first, ..rest] -> {
      case list.last(rest) {
        Ok(last) -> span_merge(first.1, last.1)
        Error(_) -> first.1
      }
    }
  }
}

fn span_merge(a: Span, b: Span) -> Span {
  case a.start_line < b.start_line || {
    a.start_line == b.start_line && a.start_col <= b.start_col
  } {
    True -> Span(a.file, a.start_line, a.start_col, b.end_line, b.end_col)
    False -> Span(b.file, b.start_line, b.start_col, a.end_line, a.end_col)
  }
}

// ============================================================================
// PUBLIC HELPERS
// ============================================================================

/// Extract the AST from a ParseResult.
pub fn result_ast(_a: a, result: ParseResult(a)) -> a {
  result.ast
}

/// Extract the errors from a ParseResult.
pub fn result_errors(_a: a, result: ParseResult(a)) -> List(ParseError) {
  result.errors
}

/// Format a parse error as a human-readable string.
pub fn error_to_string(error: ParseError) -> String {
  case error.span {
    Span(file, start_line, start_col, end_line, _) -> {
      case start_line == end_line {
        True -> "in " <> file <> " line " <> int.to_string(start_line) <> ", col " <> int.to_string(start_col)
        False -> "in " <> file <> " lines " <> int.to_string(start_line) <> "-" <> int.to_string(end_line) <> ", col " <> int.to_string(start_col)
      }
    }
  }
  <> ": "
  <> error.expected
  <> " (found: "
  <> error.got
  <> ")"
}

/// Check if an Either value is Left.
pub fn is_left(a: Either(String, a)) -> Bool {
  case a {
    Left(_) -> True
    Right(_) -> False
  }
}

/// Check if an Either value is Right.
pub fn is_right(a: Either(String, a)) -> Bool {
  case a {
    Left(_) -> False
    Right(_) -> True
  }
}

/// Extract Left value from an Either (panic if Right).
pub fn left_value(a: Either(String, a)) -> String {
  case a {
    Left(v) -> v
    Right(_) -> panic
  }
}

/// Extract Right value from an Either (panic if Left).
pub fn right_value(a: Either(String, a)) -> a {
  case a {
    Left(_) -> panic
    Right(v) -> v
  }
}
