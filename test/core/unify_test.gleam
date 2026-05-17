/// Tests for the Infer module (Bidirectional Type Checking)
import core/ast
import core/state.{new_state, with_err}
import core/unify.{unify}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s1 = Span("unify_test", 1, 1, 1, 1)

const s2 = Span("unify_test", 2, 2, 2, 2)

pub fn unify_type_mismatch_test() {
  let a = #(ast.VTyp(0), s1)
  let b = #(ast.VTyp(1), s2)
  let #(result, state) = unify(new_state, a, b)
  let error = state.TypeMismatch(a, b)
  assert result == ast.VErr
  assert state == with_err(new_state, error)
}

pub fn unify_vtyp_test() {
  let value = ast.VTyp(0)
  let a = #(value, s1)
  let b = #(value, s2)
  let #(result, state) = unify(new_state, a, b)
  assert result == value
  assert state == new_state
}

pub fn unify_vlit_test() {
  let value = ast.VLit(ast.Int(1))
  let a = #(value, s1)
  let b = #(value, s2)
  let #(result, state) = unify(new_state, a, b)
  assert result == value
  assert state == new_state
}

pub fn unify_vlitt_test() {
  let value = ast.VLitT(ast.IntT)
  let a = #(value, s1)
  let b = #(value, s2)
  let #(result, state) = unify(new_state, a, b)
  assert result == value
  assert state == new_state
}
// VCtr(tag: String, arg: Value)
// VRcd(fields: List(#(String, Value)))
// VRcdT(fields: List(#(String, Value, Option(Value))))
// VNeut(head: Head, spine: List(Elim))
// VTypeDef(name: String, params: List(#(String, Value)), constructors: List(#(String, #(List(String), Value, Term))))
// VLam( env: Env, implicits: List(#(String, Value)), param: #(String, Value), body: Term, )
// VPi( env: Env, implicits: List(#(String, Value)), domain: #(String, Value), codomain: Value, )
// VErr
