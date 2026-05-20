/// Tests for the Infer module (Bidirectional Type Checking)
import core/ast
import core/infer.{infer}
import core/state.{State, new_state, with_err}
import gleam/list
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
  assert type_ == ast.vhole(1, [])
}

pub fn infer_hole_unknown_test() {
  let new_state = State(..new_state, hole_counter: 10)
  let term = ast.Hole(-1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == State(..new_state, hole_counter: 12)
  assert result == ast.Hole(10, s0)
  assert type_ == ast.vhole(11, [])
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
  let term =
    ast.Call("f", [#(ast.float(3.14, s1), ast.float_t(s2))], ast.int_t(s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_call_arg_type_mismatch_test() {
  let term =
    ast.Call("f", [#(ast.float(3.14, s1), ast.int_t(s2))], ast.int_t(s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  let error = state.TypeMismatch(#(ast.vfloat_t, s1), #(ast.vint_t, s2))
  assert state == with_err(new_state, error)
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

pub fn infer_ann_hole_type_test() {
  let term = ast.Ann(ast.int(42, s1), ast.Hole(10, s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state
    == State(..new_state, subst: [#(10, ast.vint_t)], hole_counter: 1)
  assert result == ast.int(42, s1)
  assert type_ == ast.vint_t
}

pub fn infer_lam_zero_implicits_test() {
  // monomorphic identity
  // $fn(x: $Int) => x
  let term = ast.Lam([], #("x", ast.int_t(s1)), ast.Var(0, s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi(x: $Int) -> $Int
  assert type_ == ast.VPi([], [], #("x", ast.vint_t), ast.vint_t)
}

pub fn infer_lam_one_implicit_ref_explicit_test() {
  // polymorphic identity
  // $fn<a: $Type>(x: a) => x
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Var(0, s3),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi<a: $Type>(x: a) -> a
  assert type_
    == ast.VPi(
      [],
      [#("a", ast.VTyp(0))],
      #("x", ast.vvar(0, [])),
      ast.vvar(0, []),
    )
}

pub fn infer_lam_one_implicit_ref_implicit_test() {
  // typeof
  // $fn<a: $Type>(x: a) => a
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Var(1, s3),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi<a: $Type>(x: a) -> $Type
  assert type_
    == ast.VPi([], [#("a", ast.VTyp(0))], #("x", ast.vvar(0, [])), ast.VTyp(0))
}

pub fn infer_lam_two_implicits_test() {
  // $fn<a: $Type<0>, b: $Type<1>>(pair: ${x: a, y: b}) => {xt: a, yt: b}
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1)), #("b", ast.Typ(1, s2))],
      #(
        "pair",
        ast.RcdT(
          [#("x", ast.Var(1, s4), None), #("y", ast.Var(0, s5), None)],
          s3,
        ),
      ),
      ast.Rcd([#("xt", ast.Var(2, s7)), #("yt", ast.Var(1, s8))], s6),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi<a: $Type<0>, b: $Type<1>>(pair: ${x: a, y: b}) -> ${xt: $Type, yt: $Type}
  assert type_
    == ast.VPi(
      [],
      [#("a", ast.VTyp(0)), #("b", ast.VTyp(1))],
      #(
        "pair",
        ast.VRcdT([#("x", ast.vvar(1, []), None), #("y", ast.vvar(0, []), None)]),
      ),
      ast.VRcdT([#("xt", ast.VTyp(0), None), #("yt", ast.VTyp(1), None)]),
    )
}

pub fn infer_lam_closure_test() {
  // $let y: $Float = 3.14; $fn(x: $Int) => y
  let term = ast.Lam([], #("x", ast.int_t(s1)), ast.Var(1, s2), s0)
  let var_y = #("y", ast.vfloat(3.14), ast.vfloat_t)
  let new_state = State(..new_state, vars: [var_y])
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_
    == ast.VPi([ast.vfloat(3.14)], [], #("x", ast.vint_t), ast.vfloat_t)
  assert state == new_state
}

pub fn infer_lam_closure_shift_test() {
  // $let z = 3.14; $let y = z; $fn(x: $Int) => y
  let term = ast.Lam([], #("x", ast.int_t(s1)), ast.Var(1, s2), s0)
  let var_y = #("y", ast.vvar(1, []), ast.vfloat_t)
  let var_z = #("z", ast.vfloat(3.14), ast.vfloat_t)
  let new_state = State(..new_state, vars: [var_y, var_z])
  assert list.map(new_state.vars, fn(var) { var.0 }) == ["y", "z"]
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  let env = [ast.vvar(2, []), ast.vfloat(3.14)]
  assert type_ == ast.VPi(env, [], #("x", ast.vint_t), ast.vfloat_t)
  assert state == new_state
}
//   Lam( implicits: List(#(String, Term)), param: #(String, Term), body: Term, span: Span, )

//   Pi( implicits: List(#(String, Term)), domain: #(String, Term), codomain: Term, span: Span, )
//   Fix(name: String, body: Term, span: Span)
//   App(fun: Term, arg: Term, span: Span)

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
