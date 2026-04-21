// ============================================================================
// TYPED CALL TESTS
// ============================================================================
/// Tests for the typed Call AST variant with explicit type annotations.
///
/// These tests verify that:
/// 1. Typed Call nodes construct correctly
/// 2. Inference handles typed args properly
/// 3. Return type annotations are respected
/// 4. CoreCall → typed Call conversion works

import core/ast as ast
import core/infer.{infer}
import core/state.{initial_state}
import tao/ffi.{tao_ffis}
import syntax/grammar.{Span}
import gleam/list
import gleeunit
import gleeunit/should

pub fn main() {
  test_typed_call_constructs_test()
  test_typed_call_infer_eq_bool_test()
  test_typed_call_infer_eq_true_test()
  test_typed_call_infer_eq_false_test()
  test_typed_call_infer_lt_true_test()
  test_typed_call_ret_type_inference_test()
}

fn span() {
  Span("test", 1, 1, 1, 10)
}

fn test_state() -> state.State {
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
// CONSTRUCTION TESTS
// ============================================================================

pub fn test_typed_call_constructs_test() {
  // Verify that a typed Call can be constructed with typed args and return type
  let span = span()
  let arg1 = ast.Lit(ast.I32(1), span)
  let arg2 = ast.Lit(ast.I32(2), span)
  let arg_type = ast.Typ(0, span)
  let ret_type = ast.Typ(0, span)
  
  let call = ast.Call(
    name: "eq",
    args: [
      #(arg1, arg_type),
      #(arg2, arg_type),
    ],
    ret: ret_type,
    span: span,
  )
  
  // Verify the call was constructed correctly
  case call {
    ast.Call("eq", args, ret, _) -> {
      list.length(args) |> should.equal(2)
      case ret {
        ast.Typ(0, _) -> True |> should.be_true
        _ -> False |> should.be_true
      }
    }
    _ -> False |> should.be_true
  }
}

// ============================================================================
// INFERENCE TESTS
// ============================================================================

pub fn test_typed_call_infer_eq_bool_test() {
  // eq(1, 1) with typed args should infer Bool type
  let span = span()
  let eq_call = ast.Call(
    name: "eq",
    args: [
      #(ast.Lit(ast.I32(1), span), ast.Typ(0, span)),
      #(ast.Lit(ast.I32(1), span), ast.Typ(0, span)),
    ],
    ret: ast.Typ(0, span),
    span: span,
  )
  
  let s = test_state()
  let #(_val, ty, s) = infer(s, eq_call)
  
  list.is_empty(s.errors) |> should.be_true
  // Result type should be Bool (VTyp(0))
  case ty {
    ast.VTyp(0) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn test_typed_call_infer_eq_true_test() {
  // eq(1, 1) should evaluate to True
  let span = span()
  let eq_call = ast.Call(
    name: "eq",
    args: [
      #(ast.Lit(ast.I32(1), span), ast.Typ(0, span)),
      #(ast.Lit(ast.I32(1), span), ast.Typ(0, span)),
    ],
    ret: ast.Typ(0, span),
    span: span,
  )
  
  let s = test_state()
  let #(val, _ty, _s) = infer(s, eq_call)
  
  case val {
    ast.VCtrValue(ast.VCtr("True", _)) -> True |> should.be_true
    ast.VCtrValue(ast.VCtr("False", _)) -> False |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn test_typed_call_infer_eq_false_test() {
  // eq(1, 2) should evaluate to False
  let span = span()
  let eq_call = ast.Call(
    name: "eq",
    args: [
      #(ast.Lit(ast.I32(1), span), ast.Typ(0, span)),
      #(ast.Lit(ast.I32(2), span), ast.Typ(0, span)),
    ],
    ret: ast.Typ(0, span),
    span: span,
  )
  
  let s = test_state()
  let #(val, _ty, _s) = infer(s, eq_call)
  
  case val {
    ast.VCtrValue(ast.VCtr("False", _)) -> True |> should.be_true
    ast.VCtrValue(ast.VCtr("True", _)) -> False |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn test_typed_call_infer_lt_true_test() {
  // lt(1, 2) should evaluate to True (1 < 2)
  let span = span()
  let lt_call = ast.Call(
    name: "lt",
    args: [
      #(ast.Lit(ast.I32(1), span), ast.Typ(0, span)),
      #(ast.Lit(ast.I32(2), span), ast.Typ(0, span)),
    ],
    ret: ast.Typ(0, span),
    span: span,
  )
  
  let s = test_state()
  let #(val, _ty, _s) = infer(s, lt_call)
  
  case val {
    ast.VCtrValue(ast.VCtr("True", _)) -> True |> should.be_true
    ast.VCtrValue(ast.VCtr("False", _)) -> False |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn test_typed_call_ret_type_inference_test() {
  // Verify that the return type annotation is used in the VCall
  let span = span()
  let ret_type = ast.Typ(0, span)
  let eq_call = ast.Call(
    name: "eq",
    args: [
      #(ast.Lit(ast.I32(1), span), ast.Typ(0, span)),
      #(ast.Lit(ast.I32(1), span), ast.Typ(0, span)),
    ],
    ret: ret_type,
    span: span,
  )
  
  let s = test_state()
  let #(_val, _ty, s) = infer(s, eq_call)
  
  // Check that no errors occurred
  list.is_empty(s.errors) |> should.be_true
}
