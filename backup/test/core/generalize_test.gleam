// ============================================================================
// GENERALIZE TESTS
// ============================================================================
/// Tests for the generalize_holes function.
///
/// Generalization converts inferred holes in lambda bodies into implicit
/// type parameters, enabling polymorphic lambda inference.

import core/ast as ast
import core/state as state
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}
import core/generalize as generalize
import gleam/list

pub fn main() {
  gleeunit.main()
}

const span = Span("generalize_test", 1, 1, 1, 1)

fn vhole(id) { ast.VNeut(ast.HHole(id), []) }
fn v32(val) { ast.VLit(ast.I32(val)) }
fn make_state() { state.State(..state.initial_state, errors: [], subst: [], hole_counter: 0) }

/// Build a simple codomain Value for testing.
/// ast.Type is an alias for ast.Value.
fn codomain_value() -> ast.Value {
  ast.VPi(
    implicit: [],
    name: "x",
    env: [],
    in_val: ast.VLitT(ast.I32T),
    out_term: ast.Lam([], #("y", ast.Var(1, span)), ast.Var(0, span), span),
  )
}

// No holes to generalize
pub fn generalize_no_holes_test() {
  let domain = v32(1)
  let codomain = codomain_value()
  let #(implicit, gen_domain, gen_codomain) = generalize.generalize_holes(
    [], [], domain, codomain, make_state(), [], 0, span,
  )
  implicit |> should.equal([])
  gen_domain |> should.equal(v32(1))
  // Codomain should be quoted - VPi becomes Pi
  case gen_codomain {
    ast.Pi(_, _, _, _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// Single hole generates "_0"
pub fn generalize_one_hole_test() {
  let s = state.State(..make_state(), hole_counter: 0)
  let domain = vhole(0)
  let codomain = codomain_value()
  let s2 = state.State(..s, hole_counter: 1)
  let #(implicit, gen_domain, gen_codomain) = generalize.generalize_holes(
    [0], [], domain, codomain, s2, [], 0, span,
  )
  implicit |> should.equal(["_0"])
  gen_domain |> should.equal(vhole(0))
  case gen_codomain {
    ast.Pi(_, _, _, _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// Name collision: "_0" already used
pub fn generalize_name_collision_test() {
  let s = make_state()
  let existing = ["_0", "_1", "_2"]
  let domain = vhole(100)
  let codomain = codomain_value()
  let s2 = state.State(..s, hole_counter: 101)
  let #(implicit, _, _) = generalize.generalize_holes(
    [100], existing, domain, codomain, s2, [], 0, span,
  )
  list.length(implicit) |> should.equal(4)
  list.contains(implicit, "_3") |> should.be_true
}

// Multiple holes
pub fn generalize_multiple_holes_test() {
  let s = make_state()
  let domain = vhole(0)
  let codomain = codomain_value()
  let s2 = state.State(..s, hole_counter: 2)
  let #(implicit, _, _) = generalize.generalize_holes(
    [0, 1], [], domain, codomain, s2, [], 0, span,
  )
  list.length(implicit) |> should.equal(2)
}

// Existing + new implicit params
pub fn generalize_existing_and_new_test() {
  let s = make_state()
  let domain = vhole(10)
  let codomain = codomain_value()
  let s2 = state.State(..s, hole_counter: 11)
  let #(implicit, _, _) = generalize.generalize_holes(
    [10], ["a", "b"], domain, codomain, s2, [], 0, span,
  )
  list.length(implicit) |> should.equal(3)
  list.contains(implicit, "a") |> should.be_true
  list.contains(implicit, "b") |> should.be_true
}

// Domain is NEVER generalized
pub fn generalize_preserves_domain_test() {
  let s = make_state()
  let domain = vhole(42)
  let codomain = codomain_value()
  let s2 = state.State(..s, hole_counter: 43)
  let #(implicit, gen_domain, _) = generalize.generalize_holes(
    [42], [], domain, codomain, s2, [], 0, span,
  )
  gen_domain |> should.equal(vhole(42))
  implicit |> should.equal(["_0"])
}

// Empty holes with existing implicit
pub fn generalize_empty_holes_with_existing_test() {
  let s = make_state()
  let domain = v32(1)
  let codomain = codomain_value()
  let #(implicit, _, _) = generalize.generalize_holes(
    [], ["x", "y"], domain, codomain, s, [], 0, span,
  )
  implicit |> should.equal(["x", "y"])
}

// Name skips existing
pub fn generalize_name_skips_existing_test() {
  let s = make_state()
  let domain = vhole(10)
  let codomain = codomain_value()
  let s2 = state.State(..s, hole_counter: 11)
  let #(implicit, _, _) = generalize.generalize_holes(
    [10], ["_0", "_2"], domain, codomain, s2, [], 0, span,
  )
  list.contains(implicit, "_1") |> should.be_true
  list.contains(implicit, "_0") |> should.be_true
  list.contains(implicit, "_2") |> should.be_true
}
