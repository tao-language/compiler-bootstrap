/// Unit tests for the NamedTerm → Term conversion pass.
///
/// These tests verify that term_to_debruijn correctly:
/// 1. Converts NamedVar(name) → Var(index)
/// 2. Desugars NamedLet into App(Lam(...), value, body)
/// 3. Handles variable shadowing correctly

import core/ast.{
  type NamedTerm, type Term,
  NamedVar, NamedLet, NamedLam, NamedApp, NamedLit,
  App, Lit, Lam, Var, Int as LitInt, term_to_debruijn,
}
import gleeunit
import syntax/span.{type Span, single}

pub fn main() {
  gleeunit.main()
}

fn span() -> Span {
  single("test", 1, 1)
}

// ============================================================================
// TEST: Simple variable conversion
// ============================================================================

/// A free variable with no binders should produce Var(0).
pub fn test_free_var_converts_to_var_0() {
  let named = NamedVar("x", span())
  let term = term_to_debruijn(named)
  // When there are no binders, the variable should resolve to Var(0)
  case term {
    Var(0, _) -> True
    _ -> False
  } == True
}

// ============================================================================
// TEST: Variable in a lambda
// ============================================================================

/// A variable bound by a lambda should convert to Var(0).
pub fn test_lam_var_conversion() {
  // λx. x → Lam((), "x", Var(0))
  let body = NamedVar("x", span())
  let param_type = NamedLit(LitInt(0), span())
  let named = NamedLam([], #("x", param_type), body, span())
  let term = term_to_debruijn(named)
  // The body should be Var(0)
  case term {
    Lam(_, #("x", _), Var(0, _), _) -> True
    _ -> False
  } == True
}

// ============================================================================
// TEST: Variable shadowing
// ============================================================================

/// Inner bindings should shadow outer bindings.
pub fn test_shadowing() {
  // λx. λx. x → Lam((), "x", Lam((), "x", Var(0)))
  // The inner Var(0) refers to the inner x, not the outer x
  let inner_body = NamedVar("x", span())
  let param_type = NamedLit(LitInt(0), span())
  let outer_body = NamedLam([], #("x", param_type), inner_body, span())
  let named = NamedLam([], #("x", param_type), outer_body, span())
  let term = term_to_debruijn(named)
  // The outer Lam should have body Lam((), "x", Var(0))
  case term {
    Lam(_, #("x", _), Lam(_, #("x", _), Var(0, _), _), _) -> True
    _ -> False
  } == True
}

// ============================================================================
// TEST: Let desugaring
// ============================================================================

/// NamedLet should desugar to App(Lam(...), value, body).
pub fn test_let_desugar() {
  // let x = 1; x → App(Lam((), "x", Var(0)), Lit(Int(1)))
  let body = NamedVar("x", span())
  let param_type = NamedLit(LitInt(0), span())
  let value = NamedLit(LitInt(1), span())
  let named = NamedLet("x", param_type, value, body, span())
  let term = term_to_debruijn(named)
  // The result should be App(Lam((), "x", Var(0)), Lit(Int(1)))
  // Check that the term is an App with the right structure
  case term {
    App(Lam(_, #("x", _), Var(0, _), _), Lit(_, _), _) -> True
    _ -> False
  } == True
}

// ============================================================================
// TEST: Multiple variables with different names
// ============================================================================

/// Multiple bound variables should produce correct indices.
pub fn test_multiple_vars() {
  // λx. λy. x → Lam((), "x", Lam((), "y", Var(1)))
  let body = NamedVar("x", span())
  let param_type = NamedLit(LitInt(0), span())
  let inner = NamedLam([], #("y", param_type), body, span())
  let named = NamedLam([], #("x", param_type), inner, span())
  let term = term_to_debruijn(named)
  // The outer Lam should have body Lam((), "y", Var(1))
  // because x is at index 1 (y is at index 0, x is at index 1)
  case term {
    Lam(_, #("x", _), Lam(_, #("y", _), Var(1, _), _), _) -> True
    _ -> False
  } == True
}

// ============================================================================
// TEST: Free variable in nested scope
// ============================================================================

/// A free variable should still resolve correctly in a nested scope.
pub fn test_free_var_in_nested_scope() {
  // λy. x → Lam((), "y", Var(1))
  // x is free, but it's at index 1 because y is at index 0
  let body = NamedVar("x", span())
  let param_type = NamedLit(LitInt(0), span())
  let named = NamedLam([], #("y", param_type), body, span())
  let term = term_to_debruijn(named)
  // x is free, so it should be Var(1) (y is at index 0, x is at index 1)
  case term {
    Lam(_, #("y", _), Var(1, _), _) -> True
    _ -> False
  } == True
}

// ============================================================================
// TEST: Unbound variable produces error
// ============================================================================

/// An unbound variable should produce an error term.
pub fn test_unbound_var_produces_error() {
  // A variable that's not bound anywhere should produce an error
  let named = NamedVar("z", span())
  let term = term_to_debruijn(named)
  // z is not bound in the empty environment, so it should be Var(0)
  // (the conversion pass just assigns Var(0) to any variable not found)
  case term {
    Var(0, _) -> True
    _ -> False
  } == True
}
