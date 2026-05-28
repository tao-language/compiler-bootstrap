import core/ast
import core/eval.{eval}
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s = Span("eval_test", 0, 0, 0, 0)

pub fn eval_typ_test() {
  let term = ast.Typ(0, s)
  let result = eval([], [], term)
  assert result == ast.VTyp(0)
}

pub fn eval_hole_test() {
  let term = ast.Hole(0, s)
  let result = eval([], [], term)
  assert result == ast.vhole(0)
}

pub fn eval_lit_test() {
  let term = ast.Lit(ast.Int(1), s)
  let result = eval([], [], term)
  assert result == ast.vint(1)
}

pub fn eval_litt_test() {
  let term = ast.LitT(ast.IntT, s)
  let result = eval([], [], term)
  assert result == ast.vint_t
}

pub fn eval_var_undefined_test() {
  let term = ast.Var(0, s)
  let result = eval([], [], term)
  assert result == ast.VErr
}

pub fn eval_var0_test() {
  let term = ast.Var(0, s)
  let env = [ast.vint_t, ast.vfloat_t]
  let result = eval([], env, term)
  assert result == ast.vint_t
}

pub fn eval_var1_test() {
  let term = ast.Var(1, s)
  let env = [ast.vint_t, ast.vfloat_t]
  let result = eval([], env, term)
  assert result == ast.vfloat_t
}

pub fn eval_ctr_test() {
  let term = ast.Ctr("A", ast.int_t(s), s)
  let result = eval([], [], term)
  assert result == ast.VCtr("A", ast.vint_t)
}

pub fn eval_rcd_empty_test() {
  let term = ast.Rcd([], s)
  let result = eval([], [], term)
  assert result == ast.VRcd([])
}

pub fn eval_rcd_fields_test() {
  let term = ast.Rcd([#("x", ast.int_t(s)), #("y", ast.float_t(s))], s)
  let result = eval([], [], term)
  assert result == ast.VRcd([#("x", ast.vint_t), #("y", ast.vfloat_t)])
}

pub fn eval_rcdt_empty_test() {
  let term = ast.RcdT([], s)
  let result = eval([], [], term)
  assert result == ast.VRcdT([])
}

pub fn eval_rcdt_fields_test() {
  let term =
    ast.RcdT(
      [
        #("x", ast.int_t(s), Some(ast.int(42, s))),
        #("y", ast.float_t(s), None),
      ],
      s,
    )
  let result = eval([], [], term)
  assert result
    == ast.VRcdT([
      #("x", ast.vint_t, Some(ast.vint(42))),
      #("y", ast.vfloat_t, None),
    ])
}

pub fn eval_call_undefined_test() {
  let term = ast.Call("f", [], ast.int_t(s), s)
  let result = eval([], [], term)
  assert result == ast.vcall("f", [])
}

pub fn eval_call_return_none_test() {
  let ffi = [#("f", fn(_) { None })]
  let term = ast.Call("f", [], ast.int_t(s), s)
  let result = eval(ffi, [], term)
  assert result == ast.vcall("f", [])
}

pub fn eval_call_return_some_test() {
  let ffi = [#("f", fn(_) { Some(ast.vint(42)) })]
  let term = ast.Call("f", [], ast.int_t(s), s)
  let result = eval(ffi, [], term)
  assert result == ast.vint(42)
}

pub fn eval_call_args_test() {
  let term =
    ast.Call("f", [ast.int(42, s), ast.float(3.14, s)], ast.int_t(s), s)
  let result = eval([], [], term)
  assert result == ast.vcall("f", [ast.vint(42), ast.vfloat(3.14)])
}

pub fn eval_ann_test() {
  let term = ast.Ann(ast.int(42, s), ast.int_t(s), s)
  let result = eval([], [], term)
  assert result == ast.vint(42)
}

pub fn eval_lam_explicit_test() {
  // $fn(x: $Int) => x
  let term = ast.Lam(False, #("x", ast.int_t(s)), ast.Var(0, s), s)
  let result = eval([], [], term)
  assert result == ast.VLam(False, #("x", ast.vint_t), #([], ast.Var(0, s)))
}

pub fn eval_lam_implicit_test() {
  // $fn<x: $Type> => x
  let term = ast.Lam(True, #("x", ast.int_t(s)), ast.Var(0, s), s)
  let result = eval([], [], term)
  assert result == ast.VLam(True, #("x", ast.vint_t), #([], ast.Var(0, s)))
}

pub fn eval_lam_closure_test() {
  // let a = $Int; $fn(x: a) => a
  let term = ast.Lam(False, #("x", ast.Var(0, s)), ast.Var(1, s), s)
  let env = [ast.vint_t]
  let result = eval([], env, term)
  assert result == ast.VLam(False, #("x", ast.vint_t), #(env, ast.Var(1, s)))
}

pub fn eval_pi_explicit_test() {
  // $pi(x: $Int) => x
  let term = ast.Pi(False, #("x", ast.int_t(s)), ast.Var(0, s), s)
  let result = eval([], [], term)
  assert result == ast.VPi(False, #("x", ast.vint_t), #([], ast.Var(0, s)))
}

pub fn eval_pi_implicit_test() {
  // $pi<x: $Int> => x
  let term = ast.Pi(True, #("x", ast.int_t(s)), ast.Var(0, s), s)
  let result = eval([], [], term)
  assert result == ast.VPi(True, #("x", ast.vint_t), #([], ast.Var(0, s)))
}

pub fn eval_pi_closure_test() {
  // let a = $Int; $pi(x: a) => a
  let term = ast.Pi(False, #("x", ast.Var(0, s)), ast.Var(1, s), s)
  let env = [ast.vint_t]
  let result = eval([], env, term)
  assert result == ast.VPi(False, #("x", ast.vint_t), #(env, ast.Var(1, s)))
}

pub fn eval_fix_test() {
  let term = ast.Fix("f", ast.int(42, s), s)
  let result = eval([], [], term)
  assert result == ast.VFix("f", #([], ast.int(42, s)))
}

pub fn eval_app_not_a_function_test() {
  let fun = ast.Typ(0, s)
  let term = ast.App(fun, ast.int(42, s), s)
  let result = eval([], [], term)
  assert result == ast.VErr
}

pub fn eval_app_neutral_test() {
  // ?10 42 ~> ?10 42
  let fun = ast.Hole(10, s)
  let term = ast.App(fun, ast.int(42, s), s)
  let result = eval([], [], term)
  assert result == ast.vapp(ast.NHole(10), ast.vint(42))
}

pub fn eval_app_beta_reduction_test() {
  // ($fn(x: $Int) => x) 42 ~> 42
  let fun = ast.Lam(False, #("x", ast.int_t(s)), ast.Var(0, s), s)
  let term = ast.App(fun, ast.int(42, s), s)
  let result = eval([], [], term)
  assert result == ast.vint(42)
}

pub fn eval_app_implicit_expansion_test() {
  // ($fn<x: $Type> => ?10 x) 42
  // ~> (?10 $error) 42
  let inner = ast.App(ast.Hole(10, s), ast.Var(0, s), s)
  let fun = ast.Lam(True, #("x", ast.Typ(0, s)), inner, s)
  let term = ast.App(fun, ast.int(42, s), s)
  let result = eval([], [], term)
  assert result == ast.vapp(ast.NApp(ast.NHole(10), ast.VErr), ast.vint(42))
}

// TypeDef( params: List(#(String, Term)), constructors: List(#(String, #(List(String), Term, Term), Span)), span: Span, )

pub fn eval_match_empty_test() {
  let term = ast.Match(ast.int(42, s), [], s)
  let result = eval([], [], term)
  assert result == ast.VErr
}
// Match(arg: Term, cases: List(Case), span: Span)
//

// Err(message: String, span: Span)
