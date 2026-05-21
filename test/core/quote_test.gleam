import core/ast
import core/quote.{quote}
import core/state.{State, new_state, with_err}
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s = Span("quote_test", 0, 0, 0, 0)

pub fn quote_vtyp_test() {
  let value = ast.VTyp(0)
  let term = quote([], 0, value, s)
  assert term == ast.Typ(0, s)
}

pub fn quote_vlit_test() {
  let value = ast.VLit(ast.Int(42))
  let term = quote([], 0, value, s)
  assert term == ast.Lit(ast.Int(42), s)
}

pub fn quote_vlitt_test() {
  let value = ast.VLitT(ast.IntT)
  let term = quote([], 0, value, s)
  assert term == ast.LitT(ast.IntT, s)
}

pub fn quote_vctr_test() {
  let value = ast.VCtr("A", ast.vint(42))
  let term = quote([], 0, value, s)
  assert term == ast.Ctr("A", ast.int(42, s), s)
}

pub fn quote_vrcd_test() {
  let value = ast.VRcd([#("x", ast.vint_t), #("y", ast.vfloat_t)])
  let term = quote([], 0, value, s)
  assert term == ast.Rcd([#("x", ast.int_t(s)), #("y", ast.float_t(s))], s)
}

pub fn quote_vrcdt_test() {
  let value =
    ast.VRcdT([
      #("x", ast.vint_t, Some(ast.vint(42))),
      #("y", ast.vfloat_t, None),
    ])
  let term = quote([], 0, value, s)
  assert term
    == ast.RcdT(
      [#("x", ast.int_t(s), Some(ast.int(42, s))), #("y", ast.float_t(s), None)],
      s,
    )
}

pub fn quote_vneut_hvar_test() {
  assert quote([], 1, ast.vvar(0, []), s) == ast.Var(0, s)
  assert quote([], 2, ast.vvar(0, []), s) == ast.Var(1, s)
  assert quote([], 3, ast.vvar(0, []), s) == ast.Var(2, s)
  assert quote([], 2, ast.vvar(1, []), s) == ast.Var(0, s)
  assert quote([], 3, ast.vvar(1, []), s) == ast.Var(1, s)
  assert quote([], 4, ast.vvar(1, []), s) == ast.Var(2, s)
}

pub fn quote_vneut_hhole_test() {
  let value = ast.VNeut(ast.HHole(42), [])
  let term = quote([], 0, value, s)
  assert term == ast.Hole(42, s)
}
// VLam( env: Env, implicits: List(#(String, Value)), param: #(String, Value), body: Term, )
// VPi( env: Env, implicits: List(#(String, Value)), domain: #(String, Value), codomain: Term, )
// VTypeDef( params: List(#(String, Value)), constructors: List(#(String, #(List(String), Value, Term))), )
// VErr
