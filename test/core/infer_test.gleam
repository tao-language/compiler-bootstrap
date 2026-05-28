/// Tests for the Infer module (Bidirectional Type Checking)
import core/ast
import core/elaborate.{infer}
import core/state.{State, new_state, with_err}
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

// Helper span constants to verify error reporting.
const s0 = Span("infer_test", 0, 0, 0, 0)

const s1 = Span("infer_test", 1, 1, 1, 1)

const s2 = Span("infer_test", 2, 2, 2, 2)

const s3 = Span("infer_test", 3, 3, 3, 3)

const s4 = Span("infer_test", 4, 4, 4, 4)

const s5 = Span("infer_test", 5, 5, 5, 5)

const s6 = Span("infer_test", 6, 6, 6, 6)

const s7 = Span("infer_test", 7, 7, 7, 7)

const s8 = Span("infer_test", 8, 8, 8, 8)

pub fn infer_typ0_test() {
  let term = ast.Typ(0, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(1)
}

pub fn infer_typ1_test() {
  let term = ast.Typ(1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(2)
}

pub fn infer_hole_concrete_test() {
  let new_state = State(..new_state, hole_counter: 1)
  let term = ast.Hole(0, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == State(..new_state, hole_counter: 2)
  assert result == term
  assert type_ == ast.vhole(1)
}

pub fn infer_hole_unknown_test() {
  let new_state = State(..new_state, hole_counter: 10)
  let term = ast.Hole(-1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == State(..new_state, hole_counter: 12)
  assert result == ast.Hole(10, s0)
  assert type_ == ast.vhole(11)
}

pub fn infer_lit_int_test() {
  let term = ast.int(42, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_lit_float_test() {
  let term = ast.float(3.14, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vfloat_t
}

pub fn infer_litt_intt_test() {
  let term = ast.int_t(s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_floatt_intt_test() {
  let term = ast.float_t(s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_var_undefined_test() {
  let term = ast.Var(1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == with_err(new_state, state.VarUndefined(1, s0))
  assert result == term
  assert type_ == ast.VErr
}

pub fn infer_var0_test() {
  let vars = [#("x", ast.vint(42), ast.vint_t)]
  let new_state = State(..new_state, vars: vars)
  let term = ast.Var(0, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_var1_test() {
  let vars = [
    #("x", ast.vint(42), ast.vint_t),
    #("y", ast.vfloat(3.14), ast.vfloat_t),
  ]
  let new_state = State(..new_state, vars: vars)
  let term = ast.Var(1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vfloat_t
}

pub fn infer_ctr_test() {
  let term = ast.Ctr("A", ast.Typ(0, s0), s1)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VCtr("A", ast.VTyp(1))
}

pub fn infer_rcd0_test() {
  let term = ast.Rcd([], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VRcdT([])
}

pub fn infer_rcd1_test() {
  let term = ast.Rcd([#("x", ast.int(42, s1))], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VRcdT([#("x", ast.vint_t, None)])
}

pub fn infer_rcd2_test() {
  let term = ast.Rcd([#("x", ast.int(42, s1)), #("y", ast.float(3.14, s2))], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_
    == ast.VRcdT([#("x", ast.vint_t, None), #("y", ast.vfloat_t, None)])
}

pub fn infer_rcdt0_test() {
  let term = ast.RcdT([], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_rcdt1_test() {
  let term = ast.RcdT([#("x", ast.int_t(s1), None)], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_rcdt2_test() {
  let term =
    ast.RcdT([#("x", ast.int_t(s1), None), #("y", ast.float_t(s2), None)], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_rcdt_from_default_value_test() {
  let term = ast.RcdT([#("x", ast.int_t(s1), Some(ast.int(42, s2)))], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == ast.RcdT([#("x", ast.int_t(s1), Some(ast.int(42, s2)))], s0)
  assert type_ == ast.VTyp(0)
}

pub fn infer_call_test() {
  let term = ast.Call("f", [], ast.int_t(s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_call_args_test() {
  let term = ast.Call("f", [ast.float(3.14, s1)], ast.int_t(s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_ann_test() {
  let term = ast.Ann(ast.int(42, s1), ast.int_t(s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == ast.int(42, s1)
  assert type_ == ast.vint_t
}

pub fn infer_ann_type_mismatch_test() {
  let term = ast.Ann(ast.float(3.14, s1), ast.int_t(s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  let error = state.TypeMismatch(#(ast.vfloat_t, s1), #(ast.vint_t, s2))
  assert state == with_err(new_state, error)
  assert result == ast.float(3.14, s1)
  assert type_ == ast.vfloat_t
}
// pub fn infer_ann_hole_type_test() {
//   let term = ast.Ann(ast.int(42, s1), ast.Hole(10, s2), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state
//     == State(..new_state, subst: [#(10, ast.vint_t)], hole_counter: 1)
//   assert result == ast.int(42, s1)
//   assert type_ == ast.vint_t
// }
// pub fn infer_lam_simple_test() {
//   // $fn(x: $Int) => 3.14
//   let term = ast.Lam([], #("x", ast.int_t(s1)), ast.float(3.14, s2), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   // $pi(x: $Int) -> $Float
//   assert type_ == ast.VPi([], #("x", ast.vint_t), ast.vfloat_t)
// }

// pub fn infer_lam_identity_test() {
//   // $fn<a: $Type>(x: a) => x
//   let term =
//     ast.Lam(
//       [#("a", ast.Typ(0, s1))],
//       #("x", ast.Var(0, s2)),
//       ast.Var(0, s3),
//       s0,
//     )
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   // $pi<a: $Type>(x: a) -> a
//   assert type_
//     == ast.VPi([#("a", ast.VTyp(0))], #("x", ast.vvar(0, [])), ast.vvar(1, []))
// }

// pub fn infer_lam_typeof_test() {
//   // $fn<a: $Type>(x: a) => a
//   let term =
//     ast.Lam(
//       [#("a", ast.Typ(0, s1))],
//       #("x", ast.Var(0, s2)),
//       ast.Var(1, s3),
//       s0,
//     )
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   // $pi<a: $Type>(x: a) -> $Type
//   assert type_
//     == ast.VPi([#("a", ast.VTyp(0))], #("x", ast.vvar(0, [])), ast.VTyp(0))
// }

// pub fn infer_lam_nested_test() {
//   // $fn(x: $Int) => $fn(y: $Float) => x
//   let term_inner = ast.Lam([], #("y", ast.float_t(s3)), ast.Var(1, s4), s2)
//   let term = ast.Lam([], #("x", ast.int_t(s1)), term_inner, s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   // $pi(x: $Int) -> $pi(y: $Float) -> $Int
//   // The inner codomain is VLitT(IntT) because x: Int is its type
//   let inner_pi = ast.VPi([], #("y", ast.vfloat_t), ast.vint_t)
//   assert type_ == ast.VPi([], #("x", ast.vint_t), inner_pi)
// }

// pub fn infer_lam_nested_implicits_test() {
//   // $fn<a: $Int, b: $Float>(x: a) => $fn(y: b) => x
//   let term =
//     ast.Lam(
//       [#("a", ast.int_t(s5)), #("b", ast.float_t(s6))],
//       #("x", ast.Var(1, s1)),
//       ast.Lam([], #("y", ast.Var(1, s3)), ast.Var(1, s4), s2),
//       s0,
//     )
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   // $pi<a: $Int, b: $Float>(x: a) -> $pi(y: b) -> a
//   assert type_
//     == ast.VPi(
//       [
//         #("a", ast.vint_t),
//         #("b", ast.vfloat_t),
//       ],
//       #("x", ast.vvar(1, [])),
//       ast.VPi([], #("y", ast.vvar(1, [])), ast.vvar(3, [])),
//     )
// }

// pub fn infer_lam_closure_test() {
//   // $let z = 3.14; $let y = z; $fn(x: $Int) => y
//   let term = ast.Lam([], #("x", ast.int_t(s1)), ast.Var(1, s2), s0)
//   let var_y = #("y", ast.vvar(1, []), ast.vfloat_t)
//   let var_z = #("z", ast.vfloat(3.14), ast.vfloat_t)
//   let new_state = State(..new_state, vars: [var_y, var_z])
//   assert list.map(new_state.vars, fn(var) { var.0 }) == ["y", "z"]
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   // $pi(x: $Int) -> $Float (y's type is FloatT)
//   assert type_ == ast.VPi([], #("x", ast.vint_t), ast.vfloat_t)
// }

// pub fn infer_pi_simple_test() {
//   // $pi(x: $Int) -> $Float
//   let term = ast.Pi([], #("x", ast.int_t(s1)), ast.float_t(s2), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   assert type_ == ast.VTyp(0)
// }

// pub fn infer_pi_identity_test() {
//   // $pi<a: $Type>(x: a) -> x
//   let term =
//     ast.Pi([#("a", ast.Typ(0, s1))], #("x", ast.Var(0, s2)), ast.Var(0, s3), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   assert type_ == ast.VTyp(0)
// }

// pub fn infer_pi_typeof_test() {
//   // $pi<a: $Type>(x: a) -> a
//   let term =
//     ast.Pi([#("a", ast.Typ(0, s1))], #("x", ast.Var(0, s2)), ast.Var(1, s3), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   assert type_ == ast.VTyp(0)
// }

// pub fn infer_pi_nested_test() {
//   // $pi(x: $Int) -> $pi(y: $Float) -> x
//   let term_inner = ast.Pi([], #("y", ast.float_t(s3)), ast.Var(1, s4), s2)
//   let term = ast.Pi([], #("x", ast.int_t(s1)), term_inner, s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   assert type_ == ast.VTyp(0)
// }

// pub fn infer_pi_nested_implicits_test() {
//   // $pi<a: $Int, b: $Float>(x: a) => $pi(y: b) => x
//   let term_inner = ast.Pi([], #("y", ast.Var(1, s3)), ast.Var(1, s4), s2)
//   let term =
//     ast.Pi(
//       [#("a", ast.int_t(s5)), #("b", ast.float_t(s6))],
//       #("x", ast.Var(1, s1)),
//       term_inner,
//       s0,
//     )
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   assert type_ == ast.VTyp(0)
// }

// pub fn infer_pi_closure_test() {
//   // $let z = 3.14; $let y = z; $pi(x: $Int) -> y
//   let term = ast.Pi([], #("x", ast.int_t(s1)), ast.Var(1, s2), s0)
//   let var_y = #("y", ast.vvar(1, []), ast.vfloat_t)
//   let var_z = #("z", ast.vfloat(3.14), ast.vfloat_t)
//   let new_state = State(..new_state, vars: [var_y, var_z])
//   assert list.map(new_state.vars, fn(var) { var.0 }) == ["y", "z"]
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   assert type_ == ast.VTyp(0)
// }

// pub fn infer_fix_constant_test() {
//   let term = ast.Fix("f", ast.int(42, s1), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == State(..new_state, subst: [#(0, ast.vint_t)], hole_counter: 1)
//   assert result == term
//   assert type_ == ast.vint_t
// }

// pub fn infer_fix_unsolved_test() {
//   let term = ast.Fix("f", ast.Var(0, s1), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == State(..new_state, subst: [], hole_counter: 1)
//   assert result == term
//   assert type_ == ast.vhole(0, [])
// }

// pub fn infer_fix_annotated_test() {
//   let term = ast.Fix("f", ast.Ann(ast.Var(0, s2), ast.int_t(s3), s1), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == State(..new_state, subst: [#(0, ast.vint_t)], hole_counter: 1)
//   assert result == ast.Fix("f", ast.Var(0, s2), s0)
//   assert type_ == ast.vint_t
// }
// pub fn infer_app_error_not_a_function_test() {
//   let term = ast.App(ast.int(42, s1), ast.float(3.14, s2), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   let error = state.NotAFunction(ast.vint_t, s0)
//   assert state == State(..new_state, errors: [error])
//   assert result == ast.Err(s0)
//   assert type_ == ast.VErr
// }
// pub fn infer_app_error_arg_type_mismatch_test() {
//   let
// }
// pub fn infer_app_simple_test() {
//   // f : $pi(x: $Int) -> $Float
//   let f_type = ast.VPi([], #("x", ast.vint_t), ast.vfloat_t)
//   let vars = [#("f", ast.vvar(0, []), f_type)]
//   let new_state = State(..new_state, vars: vars)
//   let term = ast.App(ast.Var(0, s1), ast.int(42, s2), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   assert type_ == ast.vfloat_t
// }
// pub fn infer_app_identity_test() {
//   // f : $pi<a: $Type>(x: a) -> x
//   let f_type =
//     ast.VPi([#("a", ast.VTyp(0))], #("x", ast.vvar(0, [])), ast.vvar(0, []))
//   let new_state = State(..new_state, vars: [#("f", ast.vvar(0, []), f_type)])
//   let term = ast.App(ast.Var(0, s1), ast.int(42, s2), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   assert type_ == ast.vint_t
// }

// pub fn infer_app_typeof_test() {
//   // f : $pi<a: $Type>(x: a) -> a
//   let f_type =
//     ast.VPi([#("a", ast.VTyp(0))], #("x", ast.vvar(0, [])), ast.vvar(1, []))
//   let new_state = State(..new_state, vars: [#("f", ast.vvar(0, []), f_type)])
//   let term = ast.App(ast.Var(0, s1), ast.int(42, s2), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   assert type_ == ast.VTyp(0)
// }

// pub fn infer_app_multi_implicits_test() {
//   // f : $pi<a: $Int, b: $Float>(x: a) -> x
//   let f_type =
//     ast.VPi(
//       [#("a", ast.vint_t), #("b", ast.vfloat_t)],
//       #("x", ast.vvar(1, [])),
//       ast.vvar(0, []),
//     )
//   let new_state = State(..new_state, vars: [#("f", ast.vvar(0, []), f_type)])
//   let term = ast.App(ast.Var(0, s1), ast.int(42, s2), s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert state == new_state
//   assert result == term
//   assert type_ == ast.vint_t
// }

//

// pub fn infer_typedef_empty_test() {
//   let term = ast.TypeDef([], [], s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert result == term
//   assert type_ == ast.VTyp(0)
//   assert state == new_state
// }
//   TypeDef( name: String, params: List(#(String, Term)), constructors: List(#(String, #(List(String), Term, Term), Span)), span: Span, )

//   Match(arg: Term, cases: List(Case), span: Span)
//   Err(message: String, span: Span)
// --- Tests for infer_fix (fix-point recursion) ---
