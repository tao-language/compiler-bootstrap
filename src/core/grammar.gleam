// ============================================================================
// CORE LANGUAGE GRAMMAR - Phase 1: Atoms + Application
// ============================================================================
/// Minimal working grammar for core language with:
/// - Variables, numbers, holes
/// - C-style application: f(x, y)
/// - Parenthesized expressions
import core/core.{
  type Span, type Term, App, F64, Hole, I32, Lit, Span, Term, Var,
}
import gleam/float
import gleam/int
import syntax/grammar.{
  type Grammar, type Value, AstValue, ListValue, NoSeparator, SoftBreak,
  TokenValue,
}

pub fn core_grammar() -> Grammar(Term) {
  use g <- grammar.define

  g
  |> grammar.name("Core")
  |> grammar.start("Expr")
  // Tokens
  |> grammar.token("Ident")
  |> grammar.token("Number")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.token("Comma")
  |> grammar.token("Question")
  // Main expression rule
  |> grammar.rule("Expr", [
    grammar.alt(grammar.ref("App"), unwrap),
    grammar.alt(grammar.ref("Atom"), unwrap),
  ])
  // Application: f(x, y) - left-associative
  |> grammar.rule("App", [
    grammar.alt(
      grammar.seq_with_layout([
        #(grammar.ref("Atom"), NoSeparator),
        #(grammar.token_pattern("LParen"), NoSeparator),
        #(grammar.ref("ArgList"), SoftBreak),
        #(grammar.token_pattern("RParen"), NoSeparator),
      ]),
      make_application,
    ),
  ])
  // Atoms
  |> grammar.rule("Atom", [
    // Variable
    grammar.alt(grammar.token_pattern("Ident"), make_var),
    // Number literal
    grammar.alt(grammar.token_pattern("Number"), make_literal),
    // Hole: ?
    grammar.alt(grammar.token_pattern("Question"), make_hole),
    // Parenthesized expression
    grammar.alt(
      grammar.seq_with_layout([
        #(grammar.token_pattern("LParen"), NoSeparator),
        #(grammar.ref("Expr"), SoftBreak),
        #(grammar.token_pattern("RParen"), NoSeparator),
      ]),
      unwrap_parens,
    ),
  ])
  // Argument list: expr, expr, ...
  |> grammar.rule("ArgList", [
    grammar.alt(
      grammar.sep1(grammar.ref("Expr"), grammar.token_pattern("Comma")),
      make_arg_list,
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

fn identity(values) {
  values
}

fn make_arg_list(values) {
  // Return a dummy term - the actual arguments are extracted in make_application
  // This is needed because every grammar rule must return a Term
  Term(Var(0), Span("generated", 0, 0))
}

fn make_var(value) {
  // For now, use dummy index 0 and span - proper implementation would use symbol table
  Term(Var(0), Span("input", 0, 0))
}

fn make_literal(values) {
  case values {
    [TokenValue(token)] -> {
      let value = token.value
      case int.parse(value) {
        Ok(n) -> Term(Lit(I32(n)), Span("input", 0, 0))
        Error(_) -> {
          case float.parse(value) {
            Ok(f) -> Term(Lit(F64(f)), Span("input", 0, 0))
            Error(_) -> Term(Lit(I32(0)), Span("input", 0, 0))
          }
        }
      }
    }
    _ -> panic as "Expected number token"
  }
}

fn make_hole(token) {
  Term(Hole(0), Span("input", 0, 0))
}

fn make_application(values) {
  case values {
    [AstValue(fun), _, ListValue(args), _] -> fold_args(fun, args)
    _ -> panic as "Expected f(args)"
  }
}

fn fold_args(fun, args) {
  case args {
    [] -> fun
    [AstValue(first), ..rest] -> {
      let app = Term(App(fun, first), get_span(fun, first))
      fold_args(app, rest)
    }
    _ -> fun
  }
}

fn get_span(t1, t2) {
  case t1, t2 {
    Term(_, span1), Term(_, _) -> span1
  }
}
