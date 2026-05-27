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

const s = Span("unify_test", 0, 0, 0, 0)
