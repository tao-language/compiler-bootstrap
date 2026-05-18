/// Tests for the Infer module (Bidirectional Type Checking)
import core/ast
import core/infer.{infer}
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
  assert result == term
  assert type_ == ast.VTyp(1)
  assert state == new_state
}

pub fn infer_typ1_test() {
  let term = ast.Typ(1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VTyp(2)
  assert state == new_state
}

pub fn infer_hole_concrete_test() {
  let new_state = State(..new_state, hole_counter: 1)
  let term = ast.Hole(0, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.vhole(1, [])
  assert state == State(..new_state, hole_counter: 2)
}

pub fn infer_hole_unknown_test() {
  let new_state = State(..new_state, hole_counter: 10)
  let term = ast.Hole(-1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == ast.Hole(10, s0)
  assert type_ == ast.vhole(11, [])
  assert state == State(..new_state, hole_counter: 12)
}

pub fn infer_lit_int_test() {
  let term = ast.int(42, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.vint_t
  assert state == new_state
}

pub fn infer_lit_float_test() {
  let term = ast.float(3.14, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.vfloat_t
  assert state == new_state
}

pub fn infer_litt_intt_test() {
  let term = ast.int_t(s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VTyp(0)
  assert state == new_state
}

pub fn infer_floatt_intt_test() {
  let term = ast.float_t(s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VTyp(0)
  assert state == new_state
}

pub fn infer_var_undefined_test() {
  let term = ast.Var(1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VErr
  assert state == with_err(new_state, state.VarUndefined(1, s0))
}

pub fn infer_var0_test() {
  let vars = [#("x", ast.vint(42), ast.vint_t)]
  let new_state = State(..new_state, vars: vars)
  let term = ast.Var(0, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.vint_t
  assert state == new_state
}

pub fn infer_var1_test() {
  let vars = [
    #("x", ast.vint(42), ast.vint_t),
    #("y", ast.vfloat(3.14), ast.vfloat_t),
  ]
  let new_state = State(..new_state, vars: vars)
  let term = ast.Var(1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.vfloat_t
  assert state == new_state
}

pub fn infer_ctr_test() {
  let term = ast.Ctr("A", ast.Typ(0, s0), s1)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VCtr("A", ast.VTyp(1))
  assert state == new_state
}

pub fn infer_rcd0_test() {
  let term = ast.Rcd([], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VRcdT([])
  assert state == new_state
}

pub fn infer_rcd1_test() {
  let term = ast.Rcd([#("x", ast.int(42, s1))], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VRcdT([#("x", ast.vint_t, None)])
  assert state == new_state
}

pub fn infer_rcd2_test() {
  let term = ast.Rcd([#("x", ast.int(42, s1)), #("y", ast.float(3.14, s2))], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_
    == ast.VRcdT([#("x", ast.vint_t, None), #("y", ast.vfloat_t, None)])
  assert state == new_state
}

pub fn infer_rcdt0_test() {
  let term = ast.RcdT([], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VTyp(0)
  assert state == new_state
}

pub fn infer_rcdt1_test() {
  let term = ast.RcdT([#("x", ast.int_t(s1), None)], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VTyp(0)
  assert state == new_state
}

pub fn infer_rcdt2_test() {
  let term =
    ast.RcdT([#("x", ast.int_t(s1), None), #("y", ast.float_t(s2), None)], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VTyp(0)
  assert state == new_state
}

pub fn infer_rcdt_from_default_value_test() {
  let term = ast.RcdT([#("x", ast.int_t(s1), Some(ast.int(42, s2)))], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == ast.RcdT([#("x", ast.int_t(s1), Some(ast.int(42, s2)))], s0)
  assert type_ == ast.VTyp(0)
  assert state == new_state
}

pub fn infer_call_test() {
  let term = ast.Call("f", [], ast.int_t(s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.vint_t
  assert state == new_state
}

pub fn infer_call_args_test() {
  let term =
    ast.Call("f", [#(ast.float(3.14, s1), ast.float_t(s2))], ast.int_t(s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.vint_t
  assert state == new_state
}

pub fn infer_call_arg_type_mismatch_test() {
  let term =
    ast.Call("f", [#(ast.float(3.14, s1), ast.int_t(s2))], ast.int_t(s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  let error = state.TypeMismatch(#(ast.vfloat_t, s1), #(ast.vint_t, s2))
  assert result == term
  assert type_ == ast.vint_t
  assert state == with_err(new_state, error)
}

pub fn infer_ann_test() {
  let term = ast.Ann(ast.int(42, s1), ast.int_t(s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == ast.int(42, s1)
  assert type_ == ast.vint_t
  assert state == new_state
}

pub fn infer_ann_type_mismatch_test() {
  let term = ast.Ann(ast.float(3.14, s1), ast.int_t(s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  let error = state.TypeMismatch(#(ast.vfloat_t, s1), #(ast.vint_t, s2))
  assert result == ast.float(3.14, s1)
  assert type_ == ast.vfloat_t
  assert state == with_err(new_state, error)
}

pub fn infer_ann_hole_type_test() {
  let term = ast.Ann(ast.int(42, s1), ast.Hole(10, s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == ast.int(42, s1)
  assert type_ == ast.vint_t
  assert state
    == State(..new_state, subst: [#(10, ast.vint_t)], hole_counter: 1)
}

pub fn infer_lam_monomorphic_identity_test() {
  // $fn(x: $Int) => x
  let term = ast.Lam([], #("x", ast.int_t(s1)), ast.Var(0, s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  assert type_ == ast.VPi([], [], #("x", ast.vint_t), ast.vint_t)
  assert state == new_state
}

pub fn infer_lam_polymorphic_identity_test() {
  // $fn<a: $Type>(x: a) => x
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Var(0, s3),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  // $pi<a: $Type>(x: a) -> a
  assert type_
    == ast.VPi(
      [],
      [#("a", ast.VTyp(0))],
      #("x", ast.vvar(1, [])),
      ast.vvar(0, []),
    )
  assert state == new_state
}

pub fn infer_lam_polymorphic_typeof_test() {
  // $fn<a: $Type>(x: a) => a
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Var(1, s3),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert result == term
  // $pi<a: $Type>(x: a) -> $Type
  assert type_
    == ast.VPi([], [#("a", ast.VTyp(0))], #("x", ast.vvar(1, [])), ast.VTyp(0))
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
