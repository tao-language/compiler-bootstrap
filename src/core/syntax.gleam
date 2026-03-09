// ============================================================================
// CORE LANGUAGE SYNTAX - Minimal Skeleton
// ============================================================================
/// Minimal syntax definition supporting:
/// - Variables: x
/// - Literals: 42
/// - Lambda: λx. body
/// - Application: f(x)
///
/// Both parser and formatter are derived from this single grammar definition.
import core/core.{
  type Term, App, Hole, I32, Lam, Lit, Term, Var,
}
import gleam/int
import gleam/list
import gleam/result
import syntax/formatter
import syntax/grammar.{type Span, type Value, AstValue, TokenValue}
import syntax/lexer.{type Token}

// ============================================================================
// PUBLIC API
// ============================================================================

pub fn parse(source: String) -> grammar.ParseResult(Term) {
  grammar.parse(core_grammar(), source)
}

pub fn format(term: Term) -> String {
  format_term(term, -1) |> formatter.render_default
}

// ============================================================================
// GRAMMAR DEFINITION
// ============================================================================

pub fn core_grammar() -> grammar.Grammar(Term) {
  use g <- grammar.define

  g
  |> grammar.name("Core")
  |> grammar.start("Expr")
  // Tokens
  |> grammar.token("Ident")
  |> grammar.token("Number")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.token("Lambda")
  |> grammar.token("Dot")
  // Main expression rule (lowest precedence first)
  |> grammar.rule("Expr", [
    grammar.alt(grammar.ref("Lambda"), unwrap, format_term),
    grammar.alt(grammar.ref("App"), unwrap, format_term),
    grammar.alt(grammar.ref("Atom"), unwrap, format_term),
  ])
  // Lambda: λx. body
  |> grammar.rule("Lambda", [
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Lambda"),
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Dot"),
        grammar.ref("Expr"),
      ]),
      make_lambda,
      format_term,
    ),
  ])
  // Application: f(x)
  |> grammar.rule("App", [
    grammar.alt(
      grammar.seq([
        grammar.ref("Atom"),
        grammar.token_pattern("LParen"),
        grammar.ref("Expr"),
        grammar.token_pattern("RParen"),
      ]),
      make_application,
      format_term,
    ),
  ])
  // Atoms
  |> grammar.rule("Atom", [
    // Variable
    grammar.alt(grammar.token_pattern("Ident"), make_var, format_term),
    // Number literal
    grammar.alt(grammar.token_pattern("Number"), make_literal, format_term),
    // Parenthesized expression
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LParen"),
        grammar.ref("Expr"),
        grammar.token_pattern("RParen"),
      ]),
      unwrap_parens,
      format_term,
    ),
  ])
}

// ============================================================================
// CONSTRUCTOR HELPERS
// ============================================================================

fn unwrap(values) {
  case values {
    [AstValue(term)] -> term
    _ -> panic as "Expected single Term value"
  }
}

fn unwrap_parens(values) {
  case values {
    [_, AstValue(term), _] -> term
    _ -> panic as "Expected (expr)"
  }
}

fn make_lambda(values) {
  case values {
    [TokenValue(lambda_token), TokenValue(name_token), _, AstValue(body)] ->
      Term(Lam(name_token.value, body), grammar.span_from_token(lambda_token, "input"))
    _ -> panic as "Expected lambda"
  }
}

fn make_application(values) {
  case values {
    [AstValue(fun), TokenValue(lparen_token), AstValue(arg), TokenValue(rparen_token)] ->
      Term(App(fun, arg), grammar.span_from_tokens(lparen_token, rparen_token, "input"))
    _ -> panic as "Expected f(args)"
  }
}

fn make_var(values) {
  case values {
    [TokenValue(token)] -> Term(Var(0), grammar.span_from_token(token, "input"))
    _ -> panic as "Expected identifier"
  }
}

fn make_literal(values) {
  case values {
    [TokenValue(token)] -> {
      case int.parse(token.value) {
        Ok(n) -> Term(Lit(I32(n)), grammar.span_from_token(token, "input"))
        Error(_) -> Term(Lit(I32(0)), grammar.span_from_token(token, "input"))
      }
    }
    _ -> panic as "Expected number token"
  }
}

// ============================================================================
// FORMATTER
// ============================================================================

fn format_term(term: Term, parent_prec: Int) -> formatter.Doc {
  case term.data {
    Var(index) ->
      formatter.concat([
        formatter.text("var"),
        formatter.text(int.to_string(index)),
      ])
    Lit(value) -> {
      case value {
        I32(n) -> formatter.text(int.to_string(n))
        _ -> formatter.text("<lit>")
      }
    }
    Lam(name, body) -> {
      let inner =
        formatter.concat([
          formatter.text("λ"),
          formatter.text(name),
          formatter.text(". "),
          format_term(body, 70),
        ])
      wrap_parens(inner, 70 < parent_prec)
    }
    App(fun, arg) -> {
      let inner =
        formatter.concat([
          format_term(fun, 85),
          formatter.text("("),
          format_term(arg, 85),
          formatter.text(")"),
        ])
      wrap_parens(inner, 85 < parent_prec)
    }
    _ -> formatter.text("<unknown>")
  }
}

fn wrap_parens(doc, condition) {
  case condition {
    True -> formatter.parens(doc)
    False -> doc
  }
}
