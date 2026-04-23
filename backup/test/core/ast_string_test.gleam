// ============================================================================
// AST STRING TESTS
// ============================================================================
/// Tests for AST stringification functions (debug utility).

import core/ast as ast
import core/ast_string as ast_string
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

const span = Span("ast_string_test", 1, 1, 1, 1)

// ============================================================================
// LITERAL TO STRING
// ============================================================================

pub fn literal_to_string_i32_test() {
  ast_string.literal_to_string(ast.I32(42)) |> should.equal("42")
}

pub fn literal_to_string_i64_test() {
  ast_string.literal_to_string(ast.I64(999)) |> should.equal("999")
}

pub fn literal_to_string_u32_test() {
  ast_string.literal_to_string(ast.U32(100)) |> should.equal("100")
}

pub fn literal_to_string_u64_test() {
  ast_string.literal_to_string(ast.U64(200)) |> should.equal("200")
}

pub fn literal_to_string_float_test() {
  ast_string.literal_to_string(ast.F32(3.14)) |> should.equal("3.14")
}

pub fn literal_to_string_float_lit_test() {
  ast_string.literal_to_string(ast.FloatLit(2.71)) |> should.equal("2.71")
}

pub fn literal_to_string_int_lit_test() {
  ast_string.literal_to_string(ast.IntLit(42)) |> should.equal("42")
}

// ============================================================================
// LITERAL TYPE TO STRING
// ============================================================================

pub fn literal_type_to_string_i32_test() {
  ast_string.literal_type_to_string(ast.I32T) |> should.equal("I32")
}

pub fn literal_type_to_string_i64_test() {
  ast_string.literal_type_to_string(ast.I64T) |> should.equal("I64")
}

pub fn literal_type_to_string_ilitt_test() {
  ast_string.literal_type_to_string(ast.ILitT) |> should.equal("Int")
}

pub fn literal_type_to_string_fitt_test() {
  ast_string.literal_type_to_string(ast.FLitT) |> should.equal("Float")
}

// ============================================================================
// VALUE TO STRING
// ============================================================================

pub fn value_to_string_unit_test() {
  ast_string.value_to_string(ast.VUnit) |> should.equal("Unit")
}

pub fn value_to_string_type_test() {
  ast_string.value_to_string(ast.VTyp(0)) |> should.equal("Type")
}

pub fn value_to_string_hvar_test() {
  ast_string.value_to_string(ast.VNeut(ast.HVar(5), [])) |> should.equal("var[5]")
}

pub fn value_to_string_hhole_test() {
  ast_string.value_to_string(ast.VNeut(ast.HHole(42), [])) |> should.equal("hole[42]")
}

pub fn value_to_string_ctr_unit_test() {
  let v = ast.VCtrValue(ast.VCtr("True", ast.VUnit))
  ast_string.value_to_string(v) |> should.equal("True")
}

pub fn value_to_string_ctr_arg_test() {
  // VCtr with VUnit body is special-cased to return just the tag
  let v = ast.VCtrValue(ast.VCtr("Just", ast.VUnit))
  ast_string.value_to_string(v) |> should.equal("Just")
}

pub fn value_to_string_lam_test() {
  // VLam needs (List(String), String, Env, Term) - just check structure
  let v = ast.VLam(["x"], "f", [], ast.Typ(0, span))
  ast_string.value_to_string(v) |> should.equal("λ")
}

pub fn value_to_string_err_test() {
  ast_string.value_to_string(ast.VErr) |> should.equal("⊥")
}

// ============================================================================
// HEAD TO STRING
// ============================================================================

pub fn head_to_string_hvar_test() {
  ast_string.head_to_string(ast.HVar(0)) |> should.equal("var[0]")
  ast_string.head_to_string(ast.HVar(10)) |> should.equal("var[10]")
}

pub fn head_to_string_hhole_test() {
  ast_string.head_to_string(ast.HHole(1)) |> should.equal("hole[1]")
}

pub fn head_to_string_hstep_limit_test() {
  ast_string.head_to_string(ast.HStepLimit) |> should.equal("<step-limit>")
}

// ============================================================================
// TYPE TO STRING
// ============================================================================

pub fn type_to_string_type_test() {
  ast_string.type_to_string(ast.VTyp(0)) |> should.equal("Type")
}

pub fn type_to_string_hvar_test() {
  ast_string.type_to_string(ast.VNeut(ast.HVar(3), [])) |> should.equal("var[3]")
}

pub fn type_to_string_hole_test() {
  ast_string.type_to_string(ast.VNeut(ast.HHole(7), [])) |> should.equal("hole[7]")
}

pub fn type_to_string_var_test() {
  ast_string.type_to_string(ast.VCall("foo", [], ast.VUnit)) |> should.equal("foo")
}

// ============================================================================
// PATTERN TO STRING
// ============================================================================

pub fn pattern_to_string_any_test() {
  ast_string.pattern_to_string(ast.PAny(span)) |> should.equal("_")
}

pub fn pattern_to_string_unit_test() {
  ast_string.pattern_to_string(ast.PUnit(span)) |> should.equal("Unit")
}

pub fn pattern_to_string_ctr_test() {
  ast_string.pattern_to_string(ast.PCtr("Just", ast.PAny(span), span)) |> should.equal("Just(_)")
}

pub fn pattern_to_string_as_test() {
  let pat = ast.PAs(ast.PAny(span), "x", span)
  ast_string.pattern_to_string(pat) |> should.equal("x@_")
}

pub fn pattern_to_string_ptyp_test() {
  ast_string.pattern_to_string(ast.PTyp(0, span)) |> should.equal("%Type")
  ast_string.pattern_to_string(ast.PTyp(2, span)) |> should.equal("%Type2")
}

// ============================================================================
// TERM TO STRING
// ============================================================================

pub fn term_to_string_unit_test() {
  let term = ast.Unit(span)
  ast_string.term_to_string(term) |> should.equal("Unit")
}

pub fn term_to_string_var_test() {
  let term = ast.Typ(0, span)
  ast_string.term_to_string(term) |> should.equal("Type")
}

pub fn term_to_string_hole_test() {
  let term = ast.Hole(42, span)
  ast_string.term_to_string(term) |> should.equal("hole[42]")
}

pub fn term_to_string_ctr_unit_test() {
  let term = ast.Ctr("True", ast.Unit(span), span)
  ast_string.term_to_string(term) |> should.equal("True")
}

pub fn term_to_string_err_test() {
  let term = ast.Err("error message", span)
  ast_string.term_to_string(term) |> should.equal("error message")
}

