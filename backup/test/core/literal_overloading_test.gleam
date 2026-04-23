// ============================================================================
// LITERAL OVERLOADING TESTS
// ============================================================================
/// Tests for polymorphic numeric literals (IntLit, FloatLit).
///
/// Bare numeric literals (42, 3.14) are parsed as overloaded types:
/// - IntLit(n) has type ILitT — compatible with ALL integer and float types
/// - FloatLit(f) has type FLitT — compatible with ALL float types only
///
/// This allows `let x: I32 = 42` and `let y: F32 = 42` to both work,
/// while `let z: I32 = 3.14` correctly fails type checking.
import core/ast as ast
import core/state as state
import tao/ffi.{ffi_add, ffi_sub, ffi_mul, ffi_div, ffi_eq, ffi_lt, ffi_gt, ffi_lte, ffi_gte, tao_ffis}
import core/infer.{infer, check}
import core/unify.{unify_result}
import gleam/list
import gleam/option.{Some}
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

const s = state.initial_state
const s0 = Span("lit_test", 0, 0, 0, 0)
const s1 = Span("lit_test", 1, 1, 1, 1)

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TYPE INFERENCE FOR OVERLOADED LITERALS
// ============================================================================

pub fn intlit_infers_ilitt_test() {
  // IntLit(42) should infer to type ILitT
  let term = ast.Lit(ast.IntLit(42), s0)
  let #(value, typ, result_s) = infer(s, term)
  
  value |> should.equal(ast.VLit(ast.IntLit(42)))
  typ |> should.equal(ast.VLitT(ast.ILitT))
  result_s.errors |> should.equal([])
}

pub fn floatlit_infers_flitt_test() {
  // FloatLit(3.14) should infer to type FLitT
  let term = ast.Lit(ast.FloatLit(3.14), s0)
  let #(value, typ, result_s) = infer(s, term)
  
  value |> should.equal(ast.VLit(ast.FloatLit(3.14)))
  typ |> should.equal(ast.VLitT(ast.FLitT))
  result_s.errors |> should.equal([])
}

// ============================================================================
// UNIFICATION OF OVERLOADED TYPES
// ============================================================================

pub fn ilitt_unifies_with_i32t_test() {
  case unify_result(s, ast.VLitT(ast.ILitT), ast.VLitT(ast.I32T), s0, s1) {
    Ok(_) -> True
    Error(_) -> False
  } |> should.be_true
}

pub fn ilitt_unifies_with_i64t_test() {
  case unify_result(s, ast.VLitT(ast.ILitT), ast.VLitT(ast.I64T), s0, s1) {
    Ok(_) -> True
    Error(_) -> False
  } |> should.be_true
}

pub fn ilitt_unifies_with_u32t_test() {
  case unify_result(s, ast.VLitT(ast.ILitT), ast.VLitT(ast.U32T), s0, s1) {
    Ok(_) -> True
    Error(_) -> False
  } |> should.be_true
}

pub fn ilitt_unifies_with_u64t_test() {
  case unify_result(s, ast.VLitT(ast.ILitT), ast.VLitT(ast.U64T), s0, s1) {
    Ok(_) -> True
    Error(_) -> False
  } |> should.be_true
}

pub fn ilitt_unifies_with_f32t_test() {
  case unify_result(s, ast.VLitT(ast.ILitT), ast.VLitT(ast.F32T), s0, s1) {
    Ok(_) -> True
    Error(_) -> False
  } |> should.be_true
}

pub fn ilitt_unifies_with_f64t_test() {
  case unify_result(s, ast.VLitT(ast.ILitT), ast.VLitT(ast.F64T), s0, s1) {
    Ok(_) -> True
    Error(_) -> False
  } |> should.be_true
}

pub fn i32t_unifies_with_ilitt_test() {
  case unify_result(s, ast.VLitT(ast.I32T), ast.VLitT(ast.ILitT), s0, s1) {
    Ok(_) -> True
    Error(_) -> False
  } |> should.be_true
}

pub fn f64t_unifies_with_ilitt_test() {
  case unify_result(s, ast.VLitT(ast.F64T), ast.VLitT(ast.ILitT), s0, s1) {
    Ok(_) -> True
    Error(_) -> False
  } |> should.be_true
}

pub fn flitt_unifies_with_f32t_test() {
  case unify_result(s, ast.VLitT(ast.FLitT), ast.VLitT(ast.F32T), s0, s1) {
    Ok(_) -> True
    Error(_) -> False
  } |> should.be_true
}

pub fn flitt_unifies_with_f64t_test() {
  case unify_result(s, ast.VLitT(ast.FLitT), ast.VLitT(ast.F64T), s0, s1) {
    Ok(_) -> True
    Error(_) -> False
  } |> should.be_true
}

pub fn flitt_does_not_unify_with_i32t_test() {
  case unify_result(s, ast.VLitT(ast.FLitT), ast.VLitT(ast.I32T), s0, s1) {
    Ok(_) -> False
    Error(_) -> True
  } |> should.be_true
}

pub fn flitt_does_not_unify_with_i64t_test() {
  case unify_result(s, ast.VLitT(ast.FLitT), ast.VLitT(ast.I64T), s0, s1) {
    Ok(_) -> False
    Error(_) -> True
  } |> should.be_true
}

// ============================================================================
// TYPE CHECKING (COERCION)
// ============================================================================

pub fn check_intlit_against_i32t_test() {
  // IntLit(42) checked against I32T should produce VLit(I32(42))
  let term = ast.Lit(ast.IntLit(42), s0)
  let expected = ast.VLitT(ast.I32T)
  let #(value, result_s) = check(s, term, expected, s1)
  
  value |> should.equal(ast.VLit(ast.I32(42)))
  result_s.errors |> should.equal([])
}

pub fn check_intlit_against_i64t_test() {
  let term = ast.Lit(ast.IntLit(42), s0)
  let expected = ast.VLitT(ast.I64T)
  let #(value, result_s) = check(s, term, expected, s1)
  
  value |> should.equal(ast.VLit(ast.I64(42)))
  result_s.errors |> should.equal([])
}

pub fn check_intlit_against_u32t_test() {
  let term = ast.Lit(ast.IntLit(42), s0)
  let expected = ast.VLitT(ast.U32T)
  let #(value, result_s) = check(s, term, expected, s1)
  
  value |> should.equal(ast.VLit(ast.U32(42)))
  result_s.errors |> should.equal([])
}

pub fn check_intlit_against_u64t_test() {
  let term = ast.Lit(ast.IntLit(42), s0)
  let expected = ast.VLitT(ast.U64T)
  let #(value, result_s) = check(s, term, expected, s1)
  
  value |> should.equal(ast.VLit(ast.U64(42)))
  result_s.errors |> should.equal([])
}

pub fn check_intlit_against_f32t_test() {
  // Int→float coercion: IntLit(42) → F32(42.0)
  let term = ast.Lit(ast.IntLit(42), s0)
  let expected = ast.VLitT(ast.F32T)
  let #(value, result_s) = check(s, term, expected, s1)
  
  value |> should.equal(ast.VLit(ast.F32(42.0)))
  result_s.errors |> should.equal([])
}

pub fn check_intlit_against_f64t_test() {
  let term = ast.Lit(ast.IntLit(42), s0)
  let expected = ast.VLitT(ast.F64T)
  let #(value, result_s) = check(s, term, expected, s1)
  
  value |> should.equal(ast.VLit(ast.F64(42.0)))
  result_s.errors |> should.equal([])
}

pub fn check_floatlit_against_f32t_test() {
  let term = ast.Lit(ast.FloatLit(3.14), s0)
  let expected = ast.VLitT(ast.F32T)
  let #(value, result_s) = check(s, term, expected, s1)
  
  value |> should.equal(ast.VLit(ast.F32(3.14)))
  result_s.errors |> should.equal([])
}

pub fn check_floatlit_against_f64t_test() {
  let term = ast.Lit(ast.FloatLit(3.14), s0)
  let expected = ast.VLitT(ast.F64T)
  let #(value, result_s) = check(s, term, expected, s1)
  
  value |> should.equal(ast.VLit(ast.F64(3.14)))
  result_s.errors |> should.equal([])
}

pub fn check_floatlit_against_i32t_fails_test() {
  // Float literal should NOT check against integer type
  let term = ast.Lit(ast.FloatLit(3.14), s0)
  let expected = ast.VLitT(ast.I32T)
  let #(value, result_s) = check(s, term, expected, s1)
  
  value |> should.equal(ast.VErr)
  list.length(result_s.errors) |> should.equal(1)
}

pub fn check_floatlit_against_i64t_fails_test() {
  let term = ast.Lit(ast.FloatLit(3.14), s0)
  let expected = ast.VLitT(ast.I64T)
  let #(value, result_s) = check(s, term, expected, s1)
  
  value |> should.equal(ast.VErr)
  list.length(result_s.errors) |> should.equal(1)
}

// ============================================================================
// ARITHMETIC ON OVERLOADED LITERALS
// ============================================================================

pub fn ffi_add_intlit_test() {
  let result = ffi_add([ast.VLit(ast.IntLit(40)), ast.VLit(ast.IntLit(2))])
  case result {
    Some(ast.VLit(ast.IntLit(42))) -> True
    _ -> False
  } |> should.be_true
}

pub fn ffi_mul_intlit_test() {
  let result = ffi_mul([ast.VLit(ast.IntLit(6)), ast.VLit(ast.IntLit(7))])
  case result {
    Some(ast.VLit(ast.IntLit(42))) -> True
    _ -> False
  } |> should.be_true
}

pub fn ffi_sub_intlit_test() {
  let result = ffi_sub([ast.VLit(ast.IntLit(50)), ast.VLit(ast.IntLit(8))])
  case result {
    Some(ast.VLit(ast.IntLit(42))) -> True
    _ -> False
  } |> should.be_true
}

pub fn ffi_div_intlit_test() {
  let result = ffi_div([ast.VLit(ast.IntLit(84)), ast.VLit(ast.IntLit(2))])
  case result {
    Some(ast.VLit(ast.IntLit(42))) -> True
    _ -> False
  } |> should.be_true
}

pub fn ffi_add_floatlit_test() {
  // 1.1 + 2.2 in IEEE 754 = 3.3000000000000003, not exactly 3.3
  // So we just check that the result is a FloatLit, not the exact value
  let result = ffi_add([ast.VLit(ast.FloatLit(1.5)), ast.VLit(ast.FloatLit(2.5))])
  case result {
    Some(ast.VLit(ast.FloatLit(4.0))) -> True
    _ -> False
  } |> should.be_true
}

pub fn ffi_eq_intlit_test() {
  let result = ffi_eq([ast.VLit(ast.IntLit(42)), ast.VLit(ast.IntLit(42))])
  case result {
    Some(ast.VCtrValue(ast.VCtr("True", ast.VUnit))) -> True
    _ -> False
  } |> should.be_true
}

pub fn ffi_lt_intlit_test() {
  let result = ffi_lt([ast.VLit(ast.IntLit(1)), ast.VLit(ast.IntLit(2))])
  case result {
    Some(ast.VCtrValue(ast.VCtr("True", ast.VUnit))) -> True
    _ -> False
  } |> should.be_true
}

pub fn ffi_eq_floatlit_test() {
  let result = ffi_eq([ast.VLit(ast.FloatLit(3.14)), ast.VLit(ast.FloatLit(3.14))])
  case result {
    Some(ast.VCtrValue(ast.VCtr("True", ast.VUnit))) -> True
    _ -> False
  } |> should.be_true
}
