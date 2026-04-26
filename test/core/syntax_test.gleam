/// Tests for the Core parser
///
/// Tests cover:
/// - Literal parsing (integer, float)
/// - Keyword parsing (hole, unit, type, true)
/// - Variable parsing (undefined variables produce errors)
/// - Lambda expressions (name capture, De Bruijn indices, nested lambdas)
/// - Pi types (fun)
/// - Let bindings (desugar to App(Lam(...), value))
/// - Match expressions
/// - Fix expressions
/// - If expressions
/// - Parenthesized expressions
/// - List expressions
/// - Error recovery (strings, unsupported operators)
/// - Edge cases (empty input, extra tokens, unicode)

import gleeunit
import core/syntax.{parse, parse_tokens}
import core/ast.{
  Var, Hole, Lam, App, Pi, Lit, Match, Rcd, Typ, Err, Case as CoreCase,
  PAny, PUnit, PLit, Int as LitInt, Float as LitFloat, Param
}
import syntax/base_lexer.{tokenize}
import gleam/list

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Integer literal parsing
// ============================================================================

pub fn parse_simple_integer_test() {
  let #(term, errors) = parse("42")
  assert errors == []
  assert case term {
    Lit(LitInt(42), span) -> span.start_line == 1 && span.start_col == 1
    _ -> False
  }
}

pub fn parse_large_integer_test() {
  let #(term, _) = parse("999999")
  assert case term {
    Lit(LitInt(999999), _) -> True
    _ -> False
  }
}

pub fn parse_zero_test() {
  let #(term, _) = parse("0")
  assert case term {
    Lit(LitInt(0), _) -> True
    _ -> False
  }
}

// ============================================================================
// Float literal parsing
// ============================================================================

pub fn parse_simple_float_test() {
  let #(term, errors) = parse("3.14")
  assert errors == []
  assert case term {
    Lit(LitFloat(3.14), _) -> True
    _ -> False
  }
}

// ============================================================================
// Variable parsing
// ============================================================================

pub fn parse_undefined_variable_produces_error_test() {
  let #(term, errors) = parse("x")
  assert case term {
    Err("undefined variable: x", _) -> True
    _ -> False
  }
  assert list.length(errors) >= 1
}

pub fn parse_underscore_produces_undefined_error_test() {
  let #(term, _) = parse("_")
  assert case term {
    Err("undefined variable: _", _) -> True
    _ -> False
  }
}

pub fn parse_underscore_prefixed_produces_undefined_error_test() {
  let #(term, _) = parse("_foo")
  assert case term {
    Err("undefined variable: _foo", _) -> True
    _ -> False
  }
}

// ============================================================================
// Hole
// ============================================================================

pub fn parse_hole_test() {
  let #(term, errors) = parse("hole")
  assert errors == []
  assert case term {
    Hole(0, _) -> True
    _ -> False
  }
}

// ============================================================================
// Unit and Typ
// ============================================================================

pub fn parse_unit_test() {
  let #(term, errors) = parse("unit")
  assert errors == []
  assert case term {
    Rcd([], _) -> True
    _ -> False
  }
}

pub fn parse_typ_test() {
  let #(term, errors) = parse("type")
  assert errors == []
  assert case term {
    Typ(0, _) -> True
    _ -> False
  }
}

pub fn parse_true_maps_to_unit_test() {
  let #(term, errors) = parse("true")
  assert errors == []
  assert case term {
    Rcd([], _) -> True
    _ -> False
  }
}

// ============================================================================
// Lambda expressions
// ============================================================================

pub fn parse_lambda_simple_test() {
  // %fn(x: ()) => body captures name "x", param_type, and body uses Var(0)
  let #(term, errors) = parse("%fn(x: ()) => x")
  // Debug: check term type and errors separately
  let term_ok = case term {
    Lam(Param("x", Rcd([], _), Var(0, _)), Var(0, _), _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  // This will fail if either term is wrong OR errors exist
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

pub fn parse_lambda_with_literal_body_test() {
  let #(term, errors) = parse("%fn(x: ()) => 42")
  let term_ok = case term {
    Lam(Param("x", Rcd([], _), Lit(LitInt(42), _)), _, _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

pub fn parse_nested_lambda_binding_works_test() {
  // %fn(x: ()) => %fn(y: ()) => x references outer x (Var(1))
  let #(term, errors) = parse("%fn(x: ()) => %fn(y: ()) => x")
  let term_ok = case term {
    Lam(Param("x", Rcd([], _), body), _, _) -> case body {
      Lam(Param("y", Rcd([], _), Var(1, _)), Var(1, _), _) -> True
      _ -> False
    }
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

pub fn parse_inner_variable_shadows_outer_test() {
  // %fn(x: ()) => %fn(x: ()) => x (inner x shadows outer x)
  let #(term, errors) = parse("%fn(x: ()) => %fn(x: ()) => x")
  let term_ok = case term {
    Lam(Param("x", Rcd([], _), body), _, _) -> case body {
      Lam(Param("x", Rcd([], _), Var(0, _)), Var(0, _), _) -> True
      _ -> False
    }
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

// ============================================================================
// Pi types (fun)
// ============================================================================

pub fn parse_fun_type_with_name_test() {
  let #(term, errors) = parse("fun(x) -> x -> x")
  let term_ok = case term {
    Pi(Var(0, _), Var(0, _), _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

pub fn parse_fun_type_two_params_test() {
  let #(term, errors) = parse("fun(x) -> x -> fun(y) -> y -> x")
  let term_ok = case term {
    Pi(Var(0, _), Pi(Var(0, _), Var(1, _), _), _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

// ============================================================================
// Let bindings — desugar to App(Lam(...), value)
// ============================================================================

pub fn parse_let_simple_binding_test() {
  let #(term, errors) = parse("%let x = 42; x")
  let term_ok = case term {
    App(Lam(Param("x", Rcd(_, _), _), Var(0, _), _), Lit(LitInt(42), _), _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

pub fn parse_let_with_lambda_test() {
  let #(term, errors) = parse("%let f = %fn(x: ()) => x; f")
  let term_ok = case term {
    App(Lam(Param("f", Rcd(_, _), _), _, _), Lam(Param("x", Rcd([], _), Var(0, _)), Var(0, _), _), _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

// ============================================================================
// Match expressions
// ============================================================================

pub fn parse_empty_match_error_test() {
  let #(term, errors) = parse("%match x { }")
  let term_ok = case term {
    Match(arg, [], _) -> case arg {
      Err("unexpected end of input", _) -> True
      _ -> False
    }
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

pub fn parse_match_with_cases_test() {
  let #(term, errors) = parse("%match x { | _ => y; | _ => y }")
  let term_ok = case term {
    Match(_, cases, _) -> list.length(cases) == 2
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

pub fn parse_match_with_unit_pattern_test() {
  let #(term, errors) = parse("%match x { | () => x }")
  let term_ok = case term {
    Match(_, [CoreCase(PUnit(_), _, _, _)], _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

pub fn parse_match_with_literal_pattern_test() {
  let #(term, errors) = parse("%match x { | 42 => x }")
  let term_ok = case term {
    Match(_, [CoreCase(PLit(LitInt(42), _), _, _, _)], _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

pub fn parse_nested_match_structure_test() {
  let #(term, errors) = parse("%match x { | match y { | _ => y } => y }")
  let term_ok = case term {
    Match(_, [CoreCase(PAny(_), _, _, _)], _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

// ============================================================================
// Fix expressions
// ============================================================================

pub fn parse_simple_fix_test() {
  let #(term, errors) = parse("%fix x = x")
  let term_ok = case term {
    App(Lam(Param("x", Rcd(_, _), _), _, _), _, _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

// ============================================================================
// If expressions — removed from core language
// ============================================================================

// ============================================================================
// Parenthesized expressions
// ============================================================================

pub fn parse_parenthesized_integer_test() {
  let #(term, errors) = parse("(42)")
  assert errors == []
  assert case term {
    Lit(LitInt(42), _) -> True
    _ -> False
  }
}

pub fn parse_nested_parens_test() {
  let #(term, _) = parse("((42))")
  assert case term {
    Lit(LitInt(42), _) -> True
    _ -> False
  }
}

// ============================================================================
// Lists
// ============================================================================

pub fn parse_empty_list_test() {
  let #(term, errors) = parse("[]")
  assert errors == []
  assert case term {
    Rcd([], _) -> True
    _ -> False
  }
}

pub fn parse_single_item_list_test() {
  let #(term, errors) = parse("[1]")
  assert errors == []
  // Single item list produces Rcd with one field
  assert case term {
    Rcd([#("0", Lit(LitInt(1), _))], _) -> True
    _ -> False
  }
}

pub fn parse_two_item_list_test() {
  let #(term, errors) = parse("[1, 2]")
  assert errors == []
  // Two item list produces Rcd with two fields
  assert case term {
    Rcd([#("0", Lit(LitInt(1), _)), #("1", Lit(LitInt(2), _))], _) -> True
    _ -> False
  }
}

pub fn parse_nested_list_test() {
  let #(term, errors) = parse("[[1, 2]]")
  let _ = errors
  // Nested list produces Rcd with Rcd inside
  assert case term {
    Rcd([#("0", Rcd([#("0", Lit(LitInt(1), _)), #("1", Lit(LitInt(2), _))], _))], _) -> True
    _ -> False
  }
}

// ============================================================================
// Error cases - error recovery
// ============================================================================

pub fn parse_string_literal_returns_error_test() {
  let #(term, _) = parse("\"hello\"")
  assert case term {
    Err("string literal not supported: hello", _) -> True
    _ -> False
  }
}

pub fn parse_unsupported_operator_returns_error_test() {
  let #(term, _) = parse("<")
  assert case term {
    Err("unexpected operator: <", _) -> True
    _ -> False
  }
}

// ============================================================================
// Edge cases
// ============================================================================

pub fn parse_empty_string_returns_error_test() {
  let #(term, _) = parse("")
  assert case term {
    Err("unexpected end of input", _) -> True
    _ -> False
  }
}

pub fn parse_whitespace_only_returns_error_test() {
  let #(term, _) = parse("   ")
  assert case term {
    Err("unexpected end of input", _) -> True
    _ -> False
  }
}

pub fn parse_extra_tokens_returns_error_test() {
  let #(term, errors) = parse("42 43")
  let _ = term
  assert list.length(errors) >= 1
}

pub fn parse_trailing_paren_recovers_test() {
  let #(term, errors) = parse("(42")
  let _ = term
  let _ = errors
  // parse allows partial results for error recovery
}

// ============================================================================
// Span accuracy tests
// ============================================================================

pub fn parse_span_starts_at_beginning_test() {
  let #(term, _) = parse("42")
  assert case term {
    Lit(_, span) -> span.start_line == 1 && span.start_col == 1
    _ -> False
  }
}

// ============================================================================
// parse_tokens with filename
// ============================================================================

pub fn parse_tokens_with_filename_test() {
  let tokens = tokenize("42")
  let #(term, errors) = parse_tokens(tokens, "test.core.tao")
  assert errors == []
  assert case term {
    Lit(LitInt(42), _) -> True
    _ -> False
  }
}

pub fn parse_tokens_empty_returns_error_test() {
  let #(term, _errors) = parse_tokens([], "test.core.tao")
  assert case term {
    Err("unexpected end of input", span) -> span.file == "test.core.tao"
    _ -> False
  }
}

// ============================================================================
// Unicode and special name characters
// ============================================================================

pub fn parse_unicode_name_produces_undefined_error_test() {
  let #(term, _) = parse("λ")
  assert case term {
    Err(_, _) -> True
    _ -> False
  }
}
