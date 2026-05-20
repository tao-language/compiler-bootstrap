import core/ast
import core/eval.{eval}
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s0 = Span("eval_test", 0, 0, 0, 0)

const s1 = Span("eval_test", 1, 1, 1, 1)

const s2 = Span("eval_test", 2, 2, 2, 2)

const s3 = Span("eval_test", 3, 3, 3, 3)

const s4 = Span("eval_test", 4, 4, 4, 4)

const s5 = Span("eval_test", 5, 5, 5, 5)

const s6 = Span("eval_test", 6, 6, 6, 6)

const s7 = Span("eval_test", 7, 7, 7, 7)

const s8 = Span("eval_test", 8, 8, 8, 8)

pub fn eval_typ_test() {
  let term = ast.Typ(0, s0)
  let result = eval([], [], term)
  assert result == ast.VTyp(0)
}

pub fn eval_hole_test() {
  let term = ast.Hole(0, s0)
  let result = eval([], [], term)
  assert result == ast.vhole(0, [])
}

pub fn eval_lit_test() {
  let term = ast.Lit(ast.Int(1), s0)
  let result = eval([], [], term)
  assert result == ast.vint(1)
}

pub fn eval_litt_test() {
  let term = ast.LitT(ast.IntT, s0)
  let result = eval([], [], term)
  assert result == ast.vint_t
}

pub fn eval_var_undefined_test() {
  let term = ast.Var(0, s0)
  let result = eval([], [], term)
  assert result == ast.VErr
}

pub fn eval_var0_test() {
  let term = ast.Var(0, s0)
  let env = [ast.vint_t, ast.vfloat_t]
  let result = eval([], env, term)
  assert result == ast.vint_t
}

pub fn eval_var1_test() {
  let term = ast.Var(1, s0)
  let env = [ast.vint_t, ast.vfloat_t]
  let result = eval([], env, term)
  assert result == ast.vfloat_t
}

pub fn eval_ctr_test() {
  let term = ast.Ctr("A", ast.int_t(s1), s0)
  let result = eval([], [], term)
  assert result == ast.VCtr("A", ast.vint_t)
}

pub fn eval_rcd_empty_test() {
  let term = ast.Rcd([], s0)
  let result = eval([], [], term)
  assert result == ast.VRcd([])
}

pub fn eval_rcd_fields_test() {
  let term = ast.Rcd([#("x", ast.int_t(s1)), #("y", ast.float_t(s2))], s0)
  let result = eval([], [], term)
  assert result == ast.VRcd([#("x", ast.vint_t), #("y", ast.vfloat_t)])
}

pub fn eval_rcdt_empty_test() {
  let term = ast.RcdT([], s0)
  let result = eval([], [], term)
  assert result == ast.VRcdT([])
}

pub fn eval_rcdt_fields_test() {
  let term =
    ast.RcdT(
      [
        #("x", ast.int_t(s1), Some(ast.int(42, s3))),
        #("y", ast.float_t(s2), None),
      ],
      s0,
    )
  let result = eval([], [], term)
  assert result
    == ast.VRcdT([
      #("x", ast.vint_t, Some(ast.vint(42))),
      #("y", ast.vfloat_t, None),
    ])
}

pub fn eval_call_undefined_test() {
  let term = ast.Call("f", [], ast.int_t(s1), s0)
  let result = eval([], [], term)
  assert result == ast.vcall("f", [], [])
}

pub fn eval_call_return_none_test() {
  let ffi = [#("f", fn(_) { None })]
  let term = ast.Call("f", [], ast.int_t(s1), s0)
  let result = eval(ffi, [], term)
  assert result == ast.vcall("f", [], [])
}

pub fn eval_call_return_some_test() {
  let ffi = [#("f", fn(_) { Some(ast.vint(42)) })]
  let term = ast.Call("f", [], ast.int_t(s1), s0)
  let result = eval(ffi, [], term)
  assert result == ast.vint(42)
}

pub fn eval_call_args_test() {
  let term =
    ast.Call("f", [ast.int(42, s2), ast.float(3.14, s4)], ast.int_t(s1), s0)
  let result = eval([], [], term)
  assert result == ast.vcall("f", [ast.vint(42), ast.vfloat(3.14)], [])
}

pub fn eval_ann_test() {
  let term = ast.Ann(ast.int(42, s1), ast.int_t(s2), s0)
  let result = eval([], [], term)
  assert result == ast.vint(42)
}
// Lam( implicits: List(#(String, Term)), param: #(String, Term), body: Term, span: Span, )
// Pi( implicits: List(#(String, Term)), domain: #(String, Term), codomain: Term, span: Span, )
// Fix(name: String, body: Term, span: Span)
// App(fun: Term, arg: Term, span: Span)
// TypeDef( params: List(#(String, Term)), constructors: List(#(String, #(List(String), Term, Term), Span)), span: Span, )
// Match(arg: Term, cases: List(Case), span: Span)
// Err(message: String, span: Span)
