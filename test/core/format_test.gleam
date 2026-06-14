import core/ast
import core/format.{format}
import gleam/option.{None, Some}
import syntax/span.{Span}

const filename = "format_test"

const s = Span(filename, 1, 1, 1, 1)

// ============================================================================
// Simple values
// ============================================================================

pub fn format_int_test() {
  assert format(ast.int(42, s), 80, 2) == "42"
  assert format(ast.int(-7, s), 80, 2) == "-7"
}

pub fn format_float_test() {
  assert format(ast.float(3.14, s), 80, 2) == "3.14"
}

pub fn format_var_test() {
  assert format(ast.var("x", s), 80, 2) == "x"
  assert format(ast.var("foo", s), 80, 2) == "foo"
}

pub fn format_hole_test() {
  assert format(ast.hole(None, s), 80, 2) == "?"
  assert format(ast.hole(Some(42), s), 80, 2) == "?<42>"
}

pub fn format_type_universe_test() {
  assert format(ast.typ(0, s), 80, 2) == "%Type"
  assert format(ast.typ(42, s), 80, 2) == "%Type<42>"
}

pub fn format_lit_type_test() {
  assert format(ast.int_t(s), 80, 2) == "%Int"
  assert format(ast.float_t(s), 80, 2) == "%Float"
  assert format(ast.i8(s), 80, 2) == "%I8"
  assert format(ast.i16(s), 80, 2) == "%I16"
  assert format(ast.i32(s), 80, 2) == "%I32"
  assert format(ast.i64(s), 80, 2) == "%I64"
  assert format(ast.u8(s), 80, 2) == "%U8"
  assert format(ast.u16(s), 80, 2) == "%U16"
  assert format(ast.u32(s), 80, 2) == "%U32"
  assert format(ast.u64(s), 80, 2) == "%U64"
  assert format(ast.f16(s), 80, 2) == "%F16"
  assert format(ast.f32(s), 80, 2) == "%F32"
  assert format(ast.f64(s), 80, 2) == "%F64"
}

pub fn format_err_test() {
  assert format(ast.err(s), 80, 2) == "%error"
}

// ============================================================================
// Constructors and records
// ============================================================================

pub fn format_ctr_test() {
  let arg = ast.var("x", s)
  let c = ast.ctr("A", arg, s)
  assert format(c, 80, 2) == "#A(x)"
}

pub fn format_rcd_empty_test() {
  assert format(ast.rcd([], s), 80, 2) == "{}"
}

pub fn format_rcd_single_test() {
  let fields = [#("a", ast.var("x", s))]
  assert format(ast.rcd(fields, s), 80, 2) == "{a: x}"
}

pub fn format_rcd_multi_test() {
  let fields = [
    #("a", ast.var("x", s)),
    #("b", ast.var("y", s)),
  ]
  // Multi-field records should have newlines when formatted
  assert format(ast.rcd(fields, s), 80, 2) == "{\n  a: x,\n  b: y\n}"
}

pub fn format_rcdt_empty_test() {
  assert format(ast.rcd_t([], s), 80, 2) == "%{}"
}

pub fn format_rcdt_single_test() {
  let fields = [#("a", #(Some(ast.var("x", s)), None))]
  assert format(ast.rcd_t(fields, s), 80, 2) == "%{a: x}"
}

pub fn format_rcdt_with_default_test() {
  let fields = [
    #("a", #(Some(ast.var("x", s)), Some(ast.int(42, s)))),
  ]
  assert format(ast.rcd_t(fields, s), 80, 2) == "%{a: x = 42}"
}

// ============================================================================
// Annotations
// ============================================================================

pub fn format_ann_test() {
  let term = ast.var("x", s)
  let type_ = ast.var("y", s)
  let ann = ast.ann(term, type_, s)
  assert format(ann, 80, 2) == "%(x: y)"
}

// ============================================================================
// Lambdas
// ============================================================================

pub fn format_lam_explicit_test() {
  let param = #("x", Some(ast.var("y", s)))
  let body = ast.var("z", s)
  let lam = ast.lam(param, body, s)
  assert format(lam, 80, 2) == "%fn(x: y) => z"
}

pub fn format_lam_implicit_test() {
  let param = #("x", Some(ast.var("y", s)))
  let body = ast.var("z", s)
  let lam = ast.lam_implicit(param, body, s)
  assert format(lam, 80, 2) == "%fn<x: y> => z"
}

// ============================================================================
// Pi types
// ============================================================================

pub fn format_pi_explicit_test() {
  let param = #("x", Some(ast.var("y", s)))
  let codomain = ast.var("z", s)
  let pi = ast.pi(param, codomain, s)
  assert format(pi, 80, 2) == "%pi(x: y) -> z"
}

pub fn format_pi_implicit_test() {
  let param = #("x", Some(ast.var("y", s)))
  let codomain = ast.var("z", s)
  let pi = ast.pi_implicit(param, codomain, s)
  assert format(pi, 80, 2) == "%pi<x: y> -> z"
}

// ============================================================================
// Fixpoint
// ============================================================================

pub fn format_fix_test() {
  let body = ast.var("x", s)
  let fix = ast.fix("f", body, s)
  assert format(fix, 80, 2) == "%fix f. x"
}

// ============================================================================
// Applications
// ============================================================================

pub fn format_app_explicit_test() {
  let fun = ast.var("f", s)
  let arg = ast.var("x", s)
  let app = ast.app(fun, arg, s)
  assert format(app, 80, 2) == "f(x)"
}

pub fn format_app_implicit_test() {
  let fun = ast.var("f", s)
  let arg = ast.var("x", s)
  let app = ast.app_implicit(fun, arg, s)
  assert format(app, 80, 2) == "f<x>"
}

// ============================================================================
// Let bindings
// ============================================================================

pub fn format_let_test() {
  let type_ = ast.var("a", s)
  let value = ast.var("y", s)
  let body = ast.var("z", s)
  let def = #("x", Some(type_), value)
  let let_ = ast.let_(def, body, s)
  assert format(let_, 80, 2) == "%let x: a = y; z"
}
