import core/ast
import core/format.{expr}
import gleam/option.{None, Some}
import syntax/span.{Span}

const filename = "format_test"

const s = Span(filename, 1, 1, 1, 1)

// ============================================================================
// Simple values
// ============================================================================

pub fn format_int_test() {
  assert expr(ast.int(42, s), 80, 2) == "42"
  assert expr(ast.int(-7, s), 80, 2) == "-7"
}

pub fn format_float_test() {
  assert expr(ast.float(3.14, s), 80, 2) == "3.14"
}

pub fn format_var_test() {
  assert expr(ast.var("x", s), 80, 2) == "x"
  assert expr(ast.var("foo", s), 80, 2) == "foo"
}

pub fn format_hole_test() {
  assert expr(ast.hole(None, s), 80, 2) == "?"
  assert expr(ast.hole(Some(42), s), 80, 2) == "?<42>"
}

pub fn format_type_universe_test() {
  assert expr(ast.typ(0, s), 80, 2) == "%Type"
  assert expr(ast.typ(42, s), 80, 2) == "%Type<42>"
}

pub fn format_lit_type_test() {
  assert expr(ast.int_t(s), 80, 2) == "%Int"
  assert expr(ast.float_t(s), 80, 2) == "%Float"
  assert expr(ast.i8(s), 80, 2) == "%I8"
  assert expr(ast.i16(s), 80, 2) == "%I16"
  assert expr(ast.i32(s), 80, 2) == "%I32"
  assert expr(ast.i64(s), 80, 2) == "%I64"
  assert expr(ast.u8(s), 80, 2) == "%U8"
  assert expr(ast.u16(s), 80, 2) == "%U16"
  assert expr(ast.u32(s), 80, 2) == "%U32"
  assert expr(ast.u64(s), 80, 2) == "%U64"
  assert expr(ast.f16(s), 80, 2) == "%F16"
  assert expr(ast.f32(s), 80, 2) == "%F32"
  assert expr(ast.f64(s), 80, 2) == "%F64"
}

pub fn format_err_test() {
  assert expr(ast.err(s), 80, 2) == "%error"
}

// ============================================================================
// Constructors and records
// ============================================================================

pub fn format_ctr_test() {
  let arg = ast.var("x", s)
  let c = ast.ctr("A", arg, s)
  assert expr(c, 80, 2) == "#A(x)"
}

pub fn format_rcd_empty_test() {
  assert expr(ast.rcd([], None, s), 80, 2) == "{}"
}

pub fn format_rcd_single_test() {
  let fields = [#("a", #(Some(ast.var("x", s)), None))]
  assert expr(ast.rcd(fields, None, s), 80, 2) == "{a: x}"
}

pub fn format_rcd_with_default_test() {
  let fields = [
    #("a", #(Some(ast.var("x", s)), Some(ast.int(42, s)))),
  ]
  assert expr(ast.rcd(fields, None, s), 80, 2) == "{a: x = 42}"
}

// ============================================================================
// Annotations
// ============================================================================

pub fn format_ann_test() {
  let term = ast.var("x", s)
  let type_ = ast.var("y", s)
  let ann = ast.ann(term, type_, s)
  assert expr(ann, 80, 2) == "%(x: y)"
}

// ============================================================================
// Lambdas
// ============================================================================

pub fn format_lam_test() {
  let param = #("x", Some(ast.var("y", s)))
  let body = ast.var("z", s)
  let lam = ast.lam(param, body, s)
  assert expr(lam, 80, 2) == "%lam(x: y) => z"
}

// ============================================================================
// Pi types
// ============================================================================

pub fn format_pi_test() {
  let param = #("x", Some(ast.var("y", s)))
  let codomain = ast.var("z", s)
  let pi = ast.pi(param, codomain, s)
  assert expr(pi, 80, 2) == "%pi(x: y) -> z"
}

// ============================================================================
// Fixpoint
// ============================================================================

pub fn format_fix_test() {
  let body = ast.var("f", s)
  let fix = ast.fix("f", body, s)
  assert expr(fix, 80, 2) == "%fix f. f"
}

// ============================================================================
// Applications
// ============================================================================

pub fn format_app_test() {
  let fun = ast.var("f", s)
  let arg = ast.var("x", s)
  let app = ast.app(fun, arg, s)
  assert expr(app, 80, 2) == "f(x)"
}

// ============================================================================
// Let bindings
// ============================================================================

pub fn format_let_test() {
  let type_ = ast.var("a", s)
  let value = ast.var("y", s)
  let body = ast.var("z", s)
  let def = #("x", Some(type_), value)
  let let_ = ast.let_var(def, body, s)
  assert expr(let_, 80, 2) == "%let x: a = y\nz"
}
