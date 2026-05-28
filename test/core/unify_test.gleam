/// Tests for the `unify` module — higher-order unification for Core values.
///
/// These tests verify:
/// - Basic type/literal unification
/// - Hole solving with occur-check
/// - Neutral term unification with spines
/// - Record and record type unification
/// - Pi type unification
/// - Force-value integration (holes resolved before comparison)
/// - EMatch unification
import core/ast
import core/state.{State, TypeMismatch, new_state, with_err}
import core/unify.{unify}
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s1 = Span("unify_test", 1, 1, 1, 1)

const s2 = Span("unify_test", 2, 2, 2, 2)

pub fn unify_type_mismatch_test() {
  let a = ast.VTyp(0)
  let b = ast.VTyp(1)
  let #(value, state) = unify(new_state, #(a, s1), #(b, s2))
  assert state == State(..new_state, errors: [TypeMismatch(#(a, s1), #(b, s2))])
  assert value == ast.VErr
}
