/// Tests for the Infer module (Bidirectional Type Checking)
import core/ast
import core/state.{
  SpineArityMismatch, SpineElimMismatch, State, TypeMismatch, new_state,
  with_err,
}
import core/unify.{unify}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s1 = Span("unify_test", 1, 1, 1, 1)

const s2 = Span("unify_test", 2, 2, 2, 2)

const s3 = Span("unify_test", 3, 3, 3, 3)

const s4 = Span("unify_test", 4, 4, 4, 4)

pub fn unify_type_mismatch_test() {
  let a = #(ast.VTyp(0), s1)
  let b = #(ast.VTyp(1), s2)
  let state = unify(new_state, a, b)
  assert state == with_err(new_state, TypeMismatch(a, b))
}

pub fn unify_vtyp_test() {
  let a = #(ast.VTyp(0), s1)
  let b = #(ast.VTyp(0), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vlit_test() {
  let a = #(ast.VLit(ast.Int(1)), s1)
  let b = #(ast.VLit(ast.Int(1)), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vlitt_test() {
  let a = #(ast.VLitT(ast.IntT), s1)
  let b = #(ast.VLitT(ast.IntT), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vneut_same_test() {
  let a = #(ast.vvar(0, []), s1)
  let b = #(ast.vvar(0, []), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vneut_different_head_test() {
  let a = #(ast.vvar(0, []), s1)
  let b = #(ast.vvar(1, []), s2)
  let state = unify(new_state, a, b)
  assert state == with_err(new_state, TypeMismatch(a, b))
}

pub fn unify_vneut_spine_arity_mismatch_test() {
  let a = #(ast.vvar(0, [ast.EApp(ast.vint_t, s2)]), s1)
  let b = #(ast.vvar(0, []), s3)
  let state = unify(new_state, a, b)
  let error = SpineArityMismatch([ast.EApp(ast.vint_t, s2)], [])
  assert state == with_err(new_state, error)
}

pub fn unify_vneut_spine_elim_mismatch_test() {
  let a = #(ast.vvar(0, [ast.EApp(ast.vint_t, s2)]), s1)
  let b = #(ast.vvar(0, [ast.EApp(ast.vfloat_t, s4)]), s3)
  let state = unify(new_state, a, b)
  let error = TypeMismatch(#(ast.vint_t, s2), #(ast.vfloat_t, s4))
  assert state == with_err(new_state, error)
}

pub fn unify_vneut_hole_test() {
  let a = #(ast.vint_t, s1)
  let b = #(ast.vhole(42, []), s1)
  let state = unify(new_state, a, b)
  assert state == State(..state, subst: [#(42, ast.vint_t)])
}
// VNeut(head: Head, spine: List(Elim))
// VCtr(tag: String, arg: Value)
// VRcd(fields: List(#(String, Value)))
// VRcdT(fields: List(#(String, Value, Option(Value))))
// VTypeDef(name: String, params: List(#(String, Value)), constructors: List(#(String, #(List(String), Value, Term))))
// VLam( env: Env, implicits: List(#(String, Value)), param: #(String, Value), body: Term, )
// VPi( env: Env, implicits: List(#(String, Value)), domain: #(String, Value), codomain: Value, )
// VErr
