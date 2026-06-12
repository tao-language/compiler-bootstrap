import core/ast.{LitT}
import core/format
import core/literals as lit
import gleam/option.{None, Some}
import gleeunit
import syntax/span

pub fn main() {
  gleeunit.main()
}

const filename = "format_test"

fn s(r1: Int, c1: Int, r2: Int, c2: Int) -> span.Span {
  span.Span(filename, r1, c1, r2, c2)
}

// ============================================================================
// Simple values
// ============================================================================

pub fn format_int_test() {
  assert format.format(ast.int(42, s(1, 1, 1, 3))) == "42"
  assert format.format(ast.int(-7, s(1, 1, 1, 3))) == "-7"
}

pub fn format_float_test() {
  assert format.format(ast.float(3.14, s(1, 1, 1, 5))) == "3.14"
}

pub fn format_var_test() {
  assert format.format(ast.var("x", s(1, 1, 1, 2))) == "x"
  assert format.format(ast.var("foo", s(1, 1, 1, 4))) == "foo"
}

pub fn format_hole_test() {
  assert format.format(ast.hole(-1, s(1, 1, 1, 2))) == "?"
  assert format.format(ast.hole(42, s(1, 1, 1, 6))) == "?<42>"
}

pub fn format_type_universe_test() {
  assert format.format(ast.typ(0, s(1, 1, 1, 6))) == "%Type"
  assert format.format(ast.typ(42, s(1, 1, 1, 10))) == "%Type<42>"
}

pub fn format_lit_type_test() {
  assert format.format(ast.AST(LitT(lit.IntT), s(1, 1, 1, 5))) == "%Int"
  assert format.format(ast.AST(LitT(lit.FloatT), s(1, 1, 1, 7))) == "%Float"
  assert format.format(ast.AST(LitT(lit.I8), s(1, 1, 1, 4))) == "%I8"
  assert format.format(ast.AST(LitT(lit.I16), s(1, 1, 1, 5))) == "%I16"
  assert format.format(ast.AST(LitT(lit.I32), s(1, 1, 1, 5))) == "%I32"
  assert format.format(ast.AST(LitT(lit.I64), s(1, 1, 1, 5))) == "%I64"
  assert format.format(ast.AST(LitT(lit.U8), s(1, 1, 1, 4))) == "%U8"
  assert format.format(ast.AST(LitT(lit.U16), s(1, 1, 1, 5))) == "%U16"
  assert format.format(ast.AST(LitT(lit.U32), s(1, 1, 1, 5))) == "%U32"
  assert format.format(ast.AST(LitT(lit.U64), s(1, 1, 1, 5))) == "%U64"
  assert format.format(ast.AST(LitT(lit.F16), s(1, 1, 1, 5))) == "%F16"
  assert format.format(ast.AST(LitT(lit.F32), s(1, 1, 1, 5))) == "%F32"
  assert format.format(ast.AST(LitT(lit.F64), s(1, 1, 1, 5))) == "%F64"
}

pub fn format_err_test() {
  assert format.format(ast.err(s(1, 1, 1, 1))) == "%error"
}

// ============================================================================
// Constructors and records
// ============================================================================

pub fn format_ctr_test() {
  let arg = ast.var("x", s(1, 2, 1, 4))
  let c = ast.AST(ast.Ctr("A", arg), s(1, 1, 1, 6))
  assert format.format(c) == "#A(x)"
}

pub fn format_rcd_empty_test() {
  assert format.format(ast.rcd([], s(1, 1, 1, 3))) == "{}"
}

pub fn format_rcd_single_test() {
  let fields = [#("a", ast.var("x", s(1, 3, 1, 6)))]
  assert format.format(ast.rcd(fields, s(1, 1, 1, 7))) == "{a: x}"
}

pub fn format_rcd_multi_test() {
  let fields = [
    #("a", ast.var("x", s(1, 3, 1, 4))),
    #("b", ast.var("y", s(1, 7, 1, 8))),
  ]
  let result = format.format(ast.rcd(fields, s(1, 1, 1, 9)))
  // Multi-field records should have newlines when formatted
  assert result == "{\n  a: x,\n  b: y\n}"
}

pub fn format_rcdt_empty_test() {
  assert format.format(ast.rcd_t([], s(1, 1, 1, 4))) == "%{}"
}

pub fn format_rcdt_single_test() {
  let fields = [#("a", #(ast.var("x", s(1, 4, 1, 7)), None))]
  assert format.format(ast.rcd_t(fields, s(1, 1, 1, 8))) == "%{a: x}"
}

pub fn format_rcdt_with_default_test() {
  let fields = [
    #("a", #(ast.var("x", s(1, 4, 1, 7)), Some(ast.int(42, s(1, 8, 1, 10))))),
  ]
  assert format.format(ast.rcd_t(fields, s(1, 1, 1, 11))) == "%{a: x = 42}"
}

// ============================================================================
// Annotations
// ============================================================================

pub fn format_ann_test() {
  let term = ast.var("x", s(1, 2, 1, 4))
  let type_ = ast.var("y", s(1, 5, 1, 8))
  let ann = ast.ann(term, type_, s(1, 1, 1, 8))
  assert format.format(ann) == "%(x: y)"
}

// ============================================================================
// Lambdas
// ============================================================================

pub fn format_lam_explicit_test() {
  let param = #("x", ast.var("y", s(1, 6, 1, 9)))
  let body = ast.var("z", s(1, 11, 1, 15))
  let lam = ast.lam(param, body, s(1, 1, 1, 15))
  assert format.format(lam) == "%fn(x: y) => z"
}

pub fn format_lam_implicit_test() {
  let param = #("x", ast.var("y", s(1, 6, 1, 9)))
  let body = ast.var("z", s(1, 11, 1, 15))
  let lam = ast.lam_implicit(param, body, s(1, 1, 1, 15))
  assert format.format(lam) == "%fn<x: y> => z"
}

// ============================================================================
// Pi types
// ============================================================================

pub fn format_pi_explicit_test() {
  let param = #("x", ast.var("y", s(1, 6, 1, 9)))
  let codomain = ast.var("z", s(1, 11, 1, 15))
  let pi = ast.pi(param, codomain, s(1, 1, 1, 15))
  assert format.format(pi) == "%pi(x: y) -> z"
}

pub fn format_pi_implicit_test() {
  let param = #("x", ast.var("y", s(1, 6, 1, 9)))
  let codomain = ast.var("z", s(1, 11, 1, 15))
  let pi = ast.pi_implicit(param, codomain, s(1, 1, 1, 15))
  assert format.format(pi) == "%pi<x: y> -> z"
}

// ============================================================================
// Fixpoint
// ============================================================================

pub fn format_fix_test() {
  let body = ast.var("x", s(1, 7, 1, 10))
  let fix = ast.fix("f", body, s(1, 1, 1, 10))
  assert format.format(fix) == "%fix f. x"
}

// ============================================================================
// Applications
// ============================================================================

pub fn format_app_explicit_test() {
  let fun = ast.var("f", s(1, 1, 1, 2))
  let arg = ast.var("x", s(1, 2, 1, 4))
  let app = ast.app(fun, arg, s(1, 1, 1, 4))
  assert format.format(app) == "f(x)"
}

pub fn format_app_implicit_test() {
  let fun = ast.var("f", s(1, 1, 1, 2))
  let arg = ast.var("x", s(1, 2, 1, 4))
  let app = ast.app_implicit(fun, arg, s(1, 1, 1, 4))
  assert format.format(app) == "f<x>"
}

// ============================================================================
// Let bindings
// ============================================================================

pub fn format_let_test() {
  let type_ = ast.var("a", s(1, 7, 1, 10))
  let value = ast.var("y", s(1, 11, 1, 14))
  let body = ast.var("z", s(1, 14, 1, 17))
  let def = #("x", type_, value)
  let let_ = ast.let_(def, body, s(1, 1, 1, 17))
  assert format.format(let_) == "%let x: a = y; z"
}
