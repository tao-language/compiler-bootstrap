// ============================================================================
// AST TESTS
// ============================================================================
/// Tests for AST helper functions (not type definitions, which are tested
/// through inference/type-checking tests).

import core/ast as ast
import gleam/option
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

const span = Span("ast_test", 1, 1, 1, 1)

// ============================================================================
// GET SPAN
// ============================================================================

pub fn get_span_pi_test() {
  let term = ast.Pi([], "x", ast.Typ(0, span), ast.Typ(0, span), span)
  ast.get_span(term) |> should.equal(span)
}

pub fn get_span_lam_test() {
  let term = ast.Lam([], #("x", ast.Typ(0, span)), ast.Typ(0, span), span)
  ast.get_span(term) |> should.equal(span)
}

pub fn get_span_var_test() {
  let term = ast.Typ(0, span)
  ast.get_span(term) |> should.equal(span)
}

pub fn get_span_app_test() {
  let app = ast.App(
    fun: ast.Typ(0, span),
    implicit: [],
    arg: ast.Typ(1, span),
    span: span,
  )
  ast.get_span(app) |> should.equal(span)
}

// ============================================================================
// MAKE NEUT
// ============================================================================

pub fn make_neut_hole_test() {
  let v = ast.make_neut(ast.HHole(42))
  case v {
    ast.VNeut(ast.HHole(42), []) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn make_neut_var_test() {
  let v = ast.make_neut(ast.HVar(5))
  case v {
    ast.VNeut(ast.HVar(5), []) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// MAKE HOLE NEUT
// ============================================================================

pub fn make_hole_neut_test() {
  let v = ast.make_hole_neut(99)
  case v {
    ast.VNeut(ast.HHole(99), []) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// MAKE VAR NEUT
// ============================================================================

pub fn make_var_neut_test() {
  let v = ast.make_var_neut(7)
  case v {
    ast.VNeut(ast.HVar(7), []) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// ERROR TERM
// ============================================================================

pub fn error_term_test() {
  let term = ast.error_term("error message", span)
  case term {
    ast.Err(msg, term_span) -> {
      msg |> should.equal("error message")
      term_span |> should.equal(span)
    }
    _ -> False |> should.be_true
  }
}

// ============================================================================
// IS TRUE VALUE
// ============================================================================

pub fn is_true_value_true_test() {
  let v = ast.VCtrValue(ast.VCtr("True", ast.VLitT(ast.I32T)))
  ast.is_true_value(v, "True") |> should.be_true
}

pub fn is_true_value_false_test() {
  let v = ast.VCtrValue(ast.VCtr("False", ast.VLitT(ast.I32T)))
  ast.is_true_value(v, "True") |> should.be_false
}

pub fn is_true_value_non_ctr_test() {
  let v = ast.VLitT(ast.I32T)
  ast.is_true_value(v, "True") |> should.be_false
}

// ============================================================================
// IS TRUTH VALUE (alias)
// ============================================================================

pub fn is_truth_value_true_test() {
  let v = ast.VCtrValue(ast.VCtr("True", ast.VLitT(ast.I32T)))
  ast.is_truth_value(v, "True") |> should.be_true
}

pub fn is_truth_value_false_test() {
  let v = ast.VLitT(ast.I32T)
  ast.is_truth_value(v, "True") |> should.be_false
}

// ============================================================================
// SHIFT TERM
// ============================================================================

pub fn shift_term_pi_test() {
  // Shift a Pi type by 1
  let pi = ast.Pi(
    [],
    "x",
    ast.Typ(0, span),
    ast.Typ(0, span),
    span,
  )
  let shifted = ast.shift_term(pi, 1)
  // The shifted term should still be a Pi
  case shifted {
    ast.Pi(_, _, _, _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn shift_term_lam_test() {
  // Shift a lambda by 1
  let lam = ast.Lam([], #("x", ast.Typ(0, span)), ast.Typ(0, span), span)
  let shifted = ast.shift_term(lam, 1)
  // The shifted term should still be a Lam
  case shifted {
    ast.Lam(_, _, _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// SHIFT CASE
// ============================================================================

pub fn shift_case_returns_case_test() {
  let case_val = ast.Case(
    pattern: ast.PUnit,
    body: ast.Typ(0, span),
    guard: option.None,
    span: span,
  )
  let shifted = ast.shift_case(case_val, 1)
  // Shift by 1 on a simple case should still be a Case
  case shifted {
    ast.Case(_, _, _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}
