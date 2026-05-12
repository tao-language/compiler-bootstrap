/// Unit tests for NamedFix → Fix conversion via term_to_debruijn.
///
/// These tests verify that $fix expressions correctly convert from NamedTerm
/// (string names) to Term (De Bruijn indices).

import core/ast.{
  NamedVar, NamedFix, NamedLam, NamedLit, NamedMatch, NamedCase,
  NamedApp,
  Fix, Lam, Var, Lit, term_to_debruijn,
  App, Case, Match, PLit, PAny, Int as LitInt,
}
import gleam/option.{Some, None}
import gleeunit
import syntax/span.{type Span, single}

pub fn main() {
  gleeunit.main()
}

fn span() -> Span {
  single("test", 1, 1)
}

// ============================================================================
// TEST: Simple fixpoint
// ============================================================================

/// $fix x. x → Fix("x", Var(0), span)
/// The body x should resolve to Var(0) after conversion.
pub fn test_simple_fix() {
  let named = NamedFix("x", NamedVar("x", span()), span())
  let term = term_to_debruijn(named)
  assert case term {
    Fix("x", Var(0, _), _) -> True
    _ -> False
  }
}

// ============================================================================
// TEST: Fixpoint with lambda body
// ============================================================================

/// $fix f. $fn(n: $Int) => n → Fix("f", Lam("n", Var(0)), span)
pub fn test_fix_with_lambda_body() {
  let body = NamedLam(
    [],
    #("n", NamedLit(LitInt(0), span())),
    NamedVar("n", span()),
    span(),
  )
  let named = NamedFix("f", body, span())
  let term = term_to_debruijn(named)
  assert case term {
    Fix("f", Lam([], #("n", _), Var(0, _), _), _) -> True
    _ -> False
  }
}

// ============================================================================
// TEST: Fixpoint with recursive variable reference
// ============================================================================

/// $fix f. $fn(n: $Int) => f(n)
/// f should resolve to Var(1) inside the lambda (0 = n param, 1 = f fixvar)
pub fn test_fix_recursive_ref() {
  // f(n) = App(f, n)
  let app_body = NamedApp(
    NamedVar("f", span()),
    NamedVar("n", span()),
    span(),
  )
  let lambda_body = NamedLam(
    [],
    #("n", NamedLit(LitInt(0), span())),
    app_body,
    span(),
  )
  let named = NamedFix("f", lambda_body, span())
  let term = term_to_debruijn(named)
  assert case term {
    Fix("f", Lam(_, #("n", _), body, _), _) -> {
      case body {
        App(App(_, Var(1, _), _), Var(0, _), _) -> True
        _ -> False
      }
    }
    _ -> False
  }
}

// ============================================================================
// TEST: Nested fixpoint
// ============================================================================

/// $fix g. $fix f. f → Fix("g", Fix("f", Var(0)))
pub fn test_nested_fix() {
  let inner = NamedFix("f", NamedVar("f", span()), span())
  let outer = NamedFix("g", inner, span())
  let term = term_to_debruijn(outer)
  assert case term {
    Fix("g", Fix("f", Var(0, _), _), _) -> True
    _ -> False
  }
}

// ============================================================================
// TEST: Fixpoint variable in match body (the actual bug case)
// ============================================================================

/// $fix f. $fn(n: $Int) => $match n { | 0 => 1 | _ => f(n) }
/// After conversion:
/// - Fix("f", Lam("n", Match(Var(0), [Case(0 => 1), Case(_ => f(n))])))
/// - f should be Var(1) inside the match (0 = n, 1 = f)
pub fn test_fix_match_recursive() {
  // First case: 0 => 1
  let case1 = NamedCase(
    PLit(LitInt(0), span()),
    None,
    NamedLit(LitInt(1), span()),
    span(),
  )
  
  // Second case: _ => f(n)
  let app_named = NamedApp(
    NamedVar("f", span()),
    NamedVar("n", span()),
    span(),
  )
  let case2 = NamedCase(
    PAny(span()),
    None,
    app_named,
    span(),
  )
  let match_body = NamedMatch(
    NamedVar("n", span()),
    [case1, case2],
    span(),
  )
  let lambda_body = NamedLam(
    [],
    #("n", NamedLit(LitInt(0), span())),
    match_body,
    span(),
  )
  let named = NamedFix("f", lambda_body, span())
  let term = term_to_debruijn(named)
  
  // Verify the structure
  assert case term {
    Fix("f", Lam(_, #("n", _), body, _), _) -> {
      case body {
        Match(_, cases, _) ->
          case cases {
            [Case(_, _, Lit(LitInt(1), _), _), Case(_, _, App(App(_, Var(1, _), _), Var(0, _), _), _)] ->
              True
            _ -> False
          }
        _ -> False
      }
    }
    _ -> False
  }
}
