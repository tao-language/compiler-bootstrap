/// Tests for the Infer module (Bidirectional Type Checking)
import core/ast.{type AST, AST, type Data} as ast
import core/context as ctx
import core/elaborate.{infer}
import core/literals.{type Literal} as lit
import core/term.{type Term} as tm
import core/value.{type Env, type Value} as v
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

// Helper span constants to verify error reporting.
const s = Span("infer_test", 0, 0, 0, 0)

const s1 = Span("infer_test", 1, 1, 1, 1)

const s2 = Span("infer_test", 2, 2, 2, 2)

const s3 = Span("infer_test", 3, 3, 3, 3)

const s4 = Span("infer_test", 4, 4, 4, 4)

const s5 = Span("infer_test", 5, 5, 5, 5)

const s6 = Span("infer_test", 6, 6, 6, 6)

const s7 = Span("infer_test", 7, 7, 7, 7)

const s8 = Span("infer_test", 8, 8, 8, 8)

pub fn infer_typ0_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = AST(ast.Typ(0), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Typ(0)
  assert type_ == v.Typ(1)
}

pub fn infer_typ1_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = AST(ast.Typ(1), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Typ(1)
  assert type_ == v.Typ(2)
}

pub fn infer_hole_concrete_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 1)
  let term = AST(ast.Hole(0), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx.new_ctx([], [], [], [], [], [], 2)
  assert result == tm.Hole(0)
  assert type_ == v.hole(1)
}

pub fn infer_hole_unknown_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 10)
  let term = AST(ast.Hole(-1), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx.new_ctx([], [], [], [], [], [], 12)
  assert result == tm.Hole(10)
  assert type_ == v.hole(11)
}

pub fn infer_lit_int_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = AST(ast.Lit(lit.Int(42)), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Lit(lit.Int(42))
  assert type_ == v.int_t
}

pub fn infer_lit_float_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = AST(ast.Lit(lit.Float(3.14)), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Lit(lit.Float(3.14))
  assert type_ == v.float_t
}

pub fn infer_litt_intt_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = AST(ast.LitT(lit.IntT), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.LitT(lit.IntT)
  assert type_ == v.Typ(0)
}

pub fn infer_floatt_intt_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = AST(ast.LitT(lit.FloatT), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.LitT(lit.FloatT)
  assert type_ == v.Typ(0)
}

pub fn infer_var_undefined_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = AST(ast.Var("x"), s)
  let #(result, type_, state) = infer(ctx0, term)
  let error = ctx.VarUndefined("x", s)
  let expected = ctx.with_err(ctx0, error)
  assert state == expected
  assert result == tm.Err
  assert type_ == v.Err
}

pub fn infer_var0_test() {
  let vars = [v.int(42), v.float(3.14)]
  let ctx0 = ctx.new_ctx(["x", "y"], [], vars, [], [], [], 0)
  let term = AST(ast.Var("x"), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Var(0)
  assert type_ == v.int(42)
}

pub fn infer_var1_test() {
  let vars = [v.int(42), v.float(3.14)]
  let ctx0 = ctx.new_ctx(["x", "y"], [], vars, [], [], [], 0)
  let term = AST(ast.Var("y"), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Var(1)
  assert type_ == v.float(3.14)
}

pub fn infer_ctr_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let typ = AST(ast.Typ(0), s)
  let term = AST(ast.Ctr("A", typ), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Ctr("A", tm.Typ(0))
  assert type_ == v.Ctr("A", v.Typ(1))
}

pub fn infer_rcd0_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = AST(ast.Rcd([]), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Rcd([])
  assert type_ == v.RcdT([])
}

pub fn infer_rcd1_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let lit42 = AST(ast.Lit(lit.Int(42)), s)
  let term = AST(ast.Rcd([#("x", lit42)]), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Rcd([#("x", tm.Lit(lit.Int(42)))])
  assert type_ == v.RcdT([#("x", v.int_t, None)])
}

pub fn infer_rcd2_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let lit42 = AST(ast.Lit(lit.Int(42)), s)
  let lit314 = AST(ast.Lit(lit.Float(3.14)), s)
  let term = AST(ast.Rcd([#("x", lit42), #("y", lit314)]), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Rcd([
    #("x", tm.Lit(lit.Int(42))),
    #("y", tm.Lit(lit.Float(3.14))),
  ])
  assert type_
    == v.RcdT([
      #("x", v.int_t, None),
      #("y", v.float_t, None),
    ])
}

pub fn infer_rcdt0_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = AST(ast.RcdT([]), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.RcdT([])
  assert type_ == v.Typ(0)
}

pub fn infer_rcdt1_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = AST(ast.RcdT([#("x", AST(ast.LitT(lit.IntT), s), None)]), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.RcdT([#("x", tm.LitT(lit.IntT), None)])
  assert type_ == v.Typ(0)
}

pub fn infer_rcdt2_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let type_int = AST(ast.LitT(lit.IntT), s)
  let type_float = AST(ast.LitT(lit.FloatT), s)
  let term = AST(ast.RcdT([
    #("x", type_int, None),
    #("y", type_float, None),
  ]), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.RcdT([
    #("x", tm.LitT(lit.IntT), None),
    #("y", tm.LitT(lit.FloatT), None),
  ])
  assert type_ == v.Typ(0)
}

pub fn infer_rcdt_from_default_value_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let type_int = AST(ast.LitT(lit.IntT), s1)
  let default_val = AST(ast.Lit(lit.Int(42)), s2)
  let term = AST(ast.RcdT([#("x", type_int, Some(default_val))]), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.RcdT([
    #("x", tm.LitT(lit.IntT), Some(tm.Lit(lit.Int(42)))),
  ])
  assert type_ == v.Typ(0)
}

pub fn infer_call_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let return_type = AST(ast.LitT(lit.IntT), s1)
  let term = AST(ast.Call("f", [], return_type), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Call("f", [], tm.LitT(lit.IntT))
  assert type_ == v.int_t
}

pub fn infer_call_args_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let arg = AST(ast.Lit(lit.Float(3.14)), s1)
  let return_type = AST(ast.LitT(lit.IntT), s1)
  let term = AST(ast.Call("f", [arg], return_type), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Call("f", [tm.Lit(lit.Float(3.14))], tm.LitT(lit.IntT))
  assert type_ == v.int_t
}

pub fn infer_ann_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let inner = AST(ast.Lit(lit.Int(42)), s1)
  let type_ = AST(ast.LitT(lit.IntT), s2)
  let term = AST(ast.Ann(inner, type_), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Lit(lit.Int(42))
  assert type_ == v.int_t
}
// pub fn infer_ann_type_mismatch_test() {
//   let inner = AST(ast.Lit(lit.Float(3.14)), s1)
//   let type_ = AST(ast.LitT(lit.IntT), s2)
//   let term = AST(ast.Ann(inner, type_), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   let error = ctx.TypeMismatch(#(v.float_t, s1), #(v.int_t, s2))
//   assert state == ctx.with_err(ctx0, error)
//   assert result == tm.Lit(lit.Float(3.14))
//   assert type_ == v.float_t
// }
// pub fn infer_ann_hole_type_test() {
//   let inner = AST(ast.Lit(lit.Int(42)), s1)
//   let type_ = AST(ast.Hole(10), s2)
//   let term = AST(ast.Ann(inner, type_), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 1)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state
//     == ctx.new_ctx([], [], [], [], [], [], 2)
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.int_t
// }
// pub fn infer_lam_simple_test() {
//   // $fn(x: $Int) => 3.14
//   let param = AST(ast.LitT(lit.IntT), s1)
//   let body = AST(ast.Lit(lit.Float(3.14)), s2)
//   let term = AST(ast.Lam(False, #("x", param), body), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   // $pi(x: $Int) -> $Float
//   assert type_ == v.Pi(False, #("x", v.int_t), #([], tm.Lit(lit.Float(3.14))))
// }

// pub fn infer_lam_identity_test() {
//   // $fn<a: $Type>(x: a) => x
//   let body = AST(ast.Var("x"), s3)
//   let param = AST(ast.Var("a"), s2)
//   let term = AST(ast.Lam(False, #("x", param), body), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   // $pi<a: $Type>(x: a) -> a
//   assert type_
//     == v.Pi(False, #("x", v.var(0, [])), #([], tm.Var("x")))
// }

// pub fn infer_lam_typeof_test() {
//   // $fn<a: $Type>(x: a) => a
//   let body = AST(ast.Var("x"), s3)
//   let param = AST(ast.Var("a"), s2)
//   let term = AST(ast.Lam(False, #("x", param), body), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   // $pi<a: $Type>(x: a) -> $Type
//   assert type_
//     == v.Pi(False, #("x", v.Typ(0)), #([], tm.Var("x")))
// }

// pub fn infer_lam_nested_test() {
//   // $fn(x: $Int) => $fn(y: $Float) => x
//   let body = AST(ast.Var("x"), s4)
//   let param = AST(ast.LitT(lit.FloatT), s3)
//   let inner = AST(ast.Lam(False, #("y", param), body), s2)
//   let param = AST(ast.LitT(lit.IntT), s1)
//   let term = AST(ast.Lam(False, #("x", param), inner), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   // $pi(x: $Int) -> $pi(y: $Float) -> $Int
//   // The inner codomain is VLitT(IntT) because x: Int is its type
//   let inner_pi = v.Pi(False, #("y", v.float_t), #([], tm.Var("x")))
//   assert type_ == v.Pi(False, #("x", v.int_t), inner_pi)
// }

// pub fn infer_lam_nested_implicits_test() {
//   // $fn<a: $Int, b: $Float>(x: a) => $fn(y: b) => x
//   let body = AST(ast.Var("a"), s4)
//   let param = AST(ast.Var("b"), s3)
//   let inner = AST(ast.Lam(False, #("y", param), body), s2)
//   let param_a = AST(ast.LitT(lit.IntT), s5)
//   let param_b = AST(ast.LitT(lit.FloatT), s6)
//   let param_x = AST(ast.Var("a"), s1)
//   let term = AST(ast.Lam(
//     [param_a, param_b],
//     #("x", param_x),
//     inner,
//   ), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   // $pi<a: $Int, b: $Float>(x: a) -> $pi(y: b) -> a
//   assert type_
//     == v.Pi(
//       True,
//       #("x", v.int_t),
//       #([], v.Pi(False, #("y", v.float_t), #([], tm.Var("a")))),
//     )
// }

// pub fn infer_lam_closure_test() {
//   // $let z = 3.14; $let y = z; $fn(x: $Int) => y
//   let body = AST(ast.Var("y"), s2)
//   let param = AST(ast.LitT(lit.IntT), s1)
//   let term = AST(ast.Lam(False, #("x", param), body), s)
//   let var_y = v.var(1, [])
//   let var_z = v.float(3.14)
//   let ctx0 = ctx.new_ctx(["y", "z"], [var_y, var_z], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   // $pi(x: $Int) -> $Float (y's type is FloatT)
//   assert type_ == v.Pi(False, #("x", v.int_t), #([], tm.Var("y")))
// }

// pub fn infer_pi_simple_test() {
//   // $pi(x: $Int) -> $Float
//   let domain = AST(ast.LitT(lit.IntT), s1)
//   let codomain = AST(ast.LitT(lit.FloatT), s2)
//   let term = AST(ast.Pi(False, #("x", domain), codomain), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.Typ(0)
// }

// pub fn infer_pi_identity_test() {
//   // $pi<a: $Type>(x: a) -> x
//   let domain = AST(ast.Var("a"), s2)
//   let codomain = AST(ast.Var("x"), s3)
//   let term = AST(ast.Pi(False, #("x", domain), codomain), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.Typ(0)
// }

// pub fn infer_pi_typeof_test() {
//   // $pi<a: $Type>(x: a) -> a
//   let domain = AST(ast.Var("a"), s2)
//   let codomain = AST(ast.Var("x"), s3)
//   let term = AST(ast.Pi(False, #("x", domain), codomain), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.Typ(0)
// }

// pub fn infer_pi_nested_test() {
//   // $pi(x: $Int) -> $pi(y: $Float) -> x
//   let codomain = AST(ast.Var("x"), s4)
//   let domain = AST(ast.LitT(lit.FloatT), s3)
//   let inner = AST(ast.Pi(False, #("y", domain), codomain), s2)
//   let domain = AST(ast.LitT(lit.IntT), s1)
//   let term = AST(ast.Pi(False, #("x", domain), inner), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.Typ(0)
// }

// pub fn infer_pi_nested_implicits_test() {
//   // $pi<a: $Int, b: $Float>(x: a) => $pi(y: b) => x
//   let codomain = AST(ast.Var("a"), s4)
//   let domain = AST(ast.Var("b"), s3)
//   let inner = AST(ast.Pi(False, #("y", domain), codomain), s2)
//   let domain_a = AST(ast.LitT(lit.IntT), s5)
//   let domain_b = AST(ast.LitT(lit.FloatT), s6)
//   let domain_x = AST(ast.Var("a"), s1)
//   let term = AST(ast.Pi(
//     [domain_a, domain_b],
//     #("x", domain_x),
//     inner,
//   ), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.Typ(0)
// }

// pub fn infer_pi_closure_test() {
//   // $let z = 3.14; $let y = z; $pi(x: $Int) -> y
//   let codomain = AST(ast.Var("y"), s2)
//   let domain = AST(ast.LitT(lit.IntT), s1)
//   let term = AST(ast.Pi(False, #("x", domain), codomain), s)
//   let var_y = v.var(1, [])
//   let var_z = v.float(3.14)
//   let ctx0 = ctx.new_ctx(["y", "z"], [var_y, var_z], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.Typ(0)
// }

// pub fn infer_fix_constant_test() {
//   let body = AST(ast.Lit(lit.Int(42)), s1)
//   let term = AST(ast.Fix("f", body), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx.new_ctx([], [], [], [], [], [], 1)
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.int_t
// }

// pub fn infer_fix_unsolved_test() {
//   let body = AST(ast.Var("f"), s1)
//   let term = AST(ast.Fix("f", body), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx.new_ctx([], [], [], [], [], [], 1)
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.hole(0)
// }

// pub fn infer_fix_annotated_test() {
//   let body = AST(ast.Ann(
//     AST(ast.Var("f"), s2),
//     AST(ast.LitT(lit.IntT), s3),
//   ), s)
//   let term = AST(ast.Fix("f", body), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx.new_ctx([], [], [], [], [], [], 1)
//   assert result == tm.Fix("f", tm.Var("f"))
//   assert type_ == v.int_t
// }
// pub fn infer_app_error_not_a_function_test() {
//   let arg = AST(ast.Lit(lit.Float(3.14)), s2)
//   let fun = AST(ast.Lit(lit.Int(42)), s1)
//   let term = AST(ast.App(fun, arg), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   let error = ctx.NotAFunction(v.int_t, s)
//   assert state == ctx.with_err(ctx0, error)
//   assert result == tm.Err
//   assert type_ == v.Err
// }
// pub fn infer_app_error_arg_type_mismatch_test() {
//   let
// }
// pub fn infer_app_simple_test() {
//   // f : $pi(x: $Int) -> $Float
//   let f_type = v.Pi(False, #("x", v.int_t), #([], tm.Lit(lit.Float(3.14))))
//   let ctx0 = ctx.new_ctx(
//     ["f"],
//     [v.var(0, [])],
//     [f_type],
//     [],
//     [],
//     [],
//     0,
//   )
//   let arg = AST(ast.Lit(lit.Int(42)), s2)
//   let fun = AST(ast.Var("f"), s1)
//   let term = AST(ast.App(fun, arg), s)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.float_t
// }
// pub fn infer_app_identity_test() {
//   // f : $pi<a: $Type>(x: a) -> x
//   let f_type =
//     v.Pi(True, #("a", v.Typ(0)), #([], v.Pi(False, #("x", v.var(1, [])), #([], tm.Var("x")))))
//   let ctx0 = ctx.new_ctx(
//     ["f"],
//     [v.var(0, [])],
//     [f_type],
//     [],
//     [],
//     [],
//     0,
//   )
//   let arg = AST(ast.Lit(lit.Int(42)), s2)
//   let fun = AST(ast.Var("f"), s1)
//   let term = AST(ast.App(fun, arg), s)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.int_t
// }

// pub fn infer_app_typeof_test() {
//   // f : $pi<a: $Type>(x: a) -> a
//   let f_type =
//     v.Pi(True, #("a", v.Typ(0)), #([], v.Pi(False, #("x", v.var(1, [])), #([], tm.Var("x")))))
//   let ctx0 = ctx.new_ctx(
//     ["f"],
//     [v.var(0, [])],
//     [f_type],
//     [],
//     [],
//     [],
//     0,
//   )
//   let arg = AST(ast.Lit(lit.Int(42)), s2)
//   let fun = AST(ast.Var("f"), s1)
//   let term = AST(ast.App(fun, arg), s)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.Typ(0)
// }

// pub fn infer_app_multi_implicits_test() {
//   // f : $pi<a: $Int, b: $Float>(x: a) -> x
//   let f_type =
//     v.Pi(
//       True,
//       #("a", v.int_t),
//       #([], v.Pi(False, #("b", v.float_t), #([], tm.Var("a")))),
//     )
//   let ctx0 = ctx.new_ctx(
//     ["f"],
//     [v.var(0, [])],
//     [f_type],
//     [],
//     [],
//     [],
//     0,
//   )
//   let arg = AST(ast.Lit(lit.Int(42)), s2)
//   let fun = AST(ast.Var("f"), s1)
//   let term = AST(ast.App(fun, arg), s)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert state == ctx0
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.int_t
// }

//

// pub fn infer_typedef_empty_test() {
//   let term = AST(ast.TypeDef([], []), s)
//   let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
//   let #(result, type_, state) = infer(ctx0, term)
//   assert result == tm.Lit(lit.Int(42))
//   assert type_ == v.Typ(0)
//   assert state == ctx0
// }
//   TypeDef( name: String, params: List(#(String, Term)), constructors: List(#(String, #(List(String), Term, Term), Span)), span: Span, )

//   Match(arg: Term, cases: List(Case), span: Span)
//   Err(message: String, span: Span)
// --- Tests for infer_fix (fix-point recursion) ---
