// ============================================================================
// FFI BUILTIN RETURN TYPE INFERENCE TESTS
// ============================================================================
/// Tests for fixing FFI builtin return type inference.
///
/// The bug: infer_call returns the first argument's type as the result type
/// instead of deriving it from the actual result value.
/// For example: eq(1, 1) returns True, but the type is ILitT instead of Bool.
///
/// This causes type mismatches when comparing with True/False constructors.

import core/ast as ast
import core/infer.{infer}
import core/state.{initial_state}
import tao/ffi.{tao_ffis}
import gleam/list
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

fn span() {
  Span("test", 1, 1, 1, 10)
}

/// Create initial state with Bool constructors (True, False)
/// This mimics what happens when prelude/bool is loaded.
fn state_with_bool_ctrs() {
  let bool_type_ctr = #("Bool", ast.CtrDef(
    params: [],
    arg_ty: ast.Typ(0, Span("type", 0, 0, 0, 0)),
    ret_ty: ast.Typ(0, Span("type", 0, 0, 0, 0)),
  ))
  let true_ctr = #("True", ast.CtrDef(
    params: [],
    arg_ty: ast.Typ(0, Span("unit", 0, 0, 0, 0)),
    ret_ty: ast.Typ(0, Span("Bool", 0, 0, 0, 0)),
  ))
  let false_ctr = #("False", ast.CtrDef(
    params: [],
    arg_ty: ast.Typ(0, Span("unit", 0, 0, 0, 0)),
    ret_ty: ast.Typ(0, Span("Bool", 0, 0, 0, 0)),
  ))
  let ffi = list.append(initial_state.ffi, tao_ffis())
  state.State(..initial_state, ffi: ffi, ctrs: [bool_type_ctr, true_ctr, false_ctr])
}

// ============================================================================
// BASIC FFI RETURN TYPE TESTS
// ============================================================================

fn eq_call_with_types(args: List(#(ast.Term, ast.Term)), ret: ast.Term) -> ast.Term {
  ast.Call(name: "eq", args: args, ret: ret, span: span())
}

pub fn ffi_eq_returns_bool_type_test() {
  // eq(I32(1): I32, I32(1): I32) -> Bool should return value True with type Bool (VCtrValue(VCtr("Bool", VUnit)))
  let eq_call = eq_call_with_types([
    #(ast.Lit(ast.I32(1), span()), ast.Typ(0, span())),
    #(ast.Lit(ast.I32(1), span()), ast.Typ(0, span())),
  ], ast.Typ(0, span()))

  let #(_val, ty, s) = infer(state_with_bool_ctrs(), eq_call)
  list.is_empty(s.errors) |> should.be_true

  // The type should be VCtrValue(VCtr("Bool", VUnit)), not ILitT
  case ty {
    ast.VCtrValue(ast.VCtr("Bool", _)) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn ffi_lt_returns_bool_type_test() {
  // lt(I32(1): I32, I32(2): I32) -> Bool should return value True with type Bool (VCtrValue(VCtr("Bool", VUnit)))
  let lt_call = eq_call_with_types([
    #(ast.Lit(ast.I32(1), span()), ast.Typ(0, span())),
    #(ast.Lit(ast.I32(2), span()), ast.Typ(0, span())),
  ], ast.Typ(0, span()))

  let #(_val, ty, s) = infer(state_with_bool_ctrs(), lt_call)
  list.is_empty(s.errors) |> should.be_true

  // The type should be VCtrValue(VCtr("Bool", VUnit)), not ILitT
  case ty {
    ast.VCtrValue(ast.VCtr("Bool", _)) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// VALUE CORRECTNESS TESTS
// ============================================================================

pub fn ffi_eq_true_value_test() {
  // eq(I32(1): I32, I32(1): I32) -> Bool should evaluate to True
  let eq_call = eq_call_with_types([
    #(ast.Lit(ast.I32(1), span()), ast.Typ(0, span())),
    #(ast.Lit(ast.I32(1), span()), ast.Typ(0, span())),
  ], ast.Typ(0, span()))

  let #(val, ty, s) = infer(state_with_bool_ctrs(), eq_call)
  list.is_empty(s.errors) |> should.be_true

  case val {
    ast.VCtrValue(ast.VCtr("True", _)) -> True |> should.be_true
    ast.VCtrValue(ast.VCtr("False", _)) -> False |> should.be_true
    _ -> False |> should.be_true
  }

  // Also verify type is correct (VCtrValue(VCtr("Bool", VUnit)) = Bool)
  case ty {
    ast.VCtrValue(ast.VCtr("Bool", _)) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn ffi_eq_false_value_test() {
  // eq(I32(1): I32, I32(2): I32) -> Bool should evaluate to False
  let eq_call = eq_call_with_types([
    #(ast.Lit(ast.I32(1), span()), ast.Typ(0, span())),
    #(ast.Lit(ast.I32(2), span()), ast.Typ(0, span())),
  ], ast.Typ(0, span()))

  let #(val, ty, s) = infer(state_with_bool_ctrs(), eq_call)
  list.is_empty(s.errors) |> should.be_true

  case val {
    ast.VCtrValue(ast.VCtr("False", _)) -> True |> should.be_true
    _ -> False |> should.be_true
  }

  // Also verify type is correct (VCtrValue(VCtr("Bool", VUnit)) = Bool)
  case ty {
    ast.VCtrValue(ast.VCtr("Bool", _)) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// EDGE CASE: Overloaded literals
// ============================================================================

pub fn ffi_eq_with_overloaded_literals_test() {
  // eq(IntLit(1): I32, IntLit(1): I32) should still work with overloaded literals
  let eq_call = eq_call_with_types([
    #(ast.Lit(ast.IntLit(1), span()), ast.Typ(0, span())),
    #(ast.Lit(ast.IntLit(1), span()), ast.Typ(0, span())),
  ], ast.Typ(0, span()))

  let #(val, ty, s) = infer(state_with_bool_ctrs(), eq_call)
  list.is_empty(s.errors) |> should.be_true

  case val {
    ast.VCtrValue(ast.VCtr("True", _)) -> True |> should.be_true
    ast.VCtrValue(ast.VCtr("False", _)) -> False |> should.be_true
    _ -> False |> should.be_true
  }

  // Type should be VCtrValue(VCtr("Bool", VUnit)) (Bool), not VLitT(ILitT)
  case ty {
    ast.VCtrValue(ast.VCtr("Bool", _)) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// EDGE CASE: Float comparison
// ============================================================================

pub fn ffi_eq_with_floats_test() {
  // eq with float literals - note: FFI eq handles F64
  let eq_call = eq_call_with_types([
    #(ast.Lit(ast.F64(1.0), span()), ast.Typ(0, span())),
    #(ast.Lit(ast.F64(1.0), span()), ast.Typ(0, span())),
  ], ast.Typ(0, span()))

  let #(val, ty, s) = infer(state_with_bool_ctrs(), eq_call)
  list.is_empty(s.errors) |> should.be_true

  case val {
    ast.VCtrValue(ast.VCtr("True", _)) -> True |> should.be_true
    ast.VCtrValue(ast.VCtr("False", _)) -> False |> should.be_true
    _ -> False |> should.be_true
  }

  case ty {
    ast.VCtrValue(ast.VCtr("Bool", _)) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}
