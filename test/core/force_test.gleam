// ============================================================================
// FORCE TESTS
// ============================================================================
/// Tests for the force function.
///
/// Force resolves holes through a substitution, recursively.
/// It's used during type checking to get concrete types from holes.
import core/core as c
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

const s1 = Span("force_test", 1, 1, 1, 1)

const v32t = c.VLitT(c.I32T)

fn vhole(i) {
  c.VNeut(c.HHole(i), [])
}

// ============================================================================
// BASIC FORCE
// ============================================================================

pub fn force_no_hole_test() {
  // Force on a value without holes returns the same value
  c.force(c.ffi_build, [], v32t) |> should.equal(v32t)
  c.force(c.ffi_build, [], c.VTyp(0)) |> should.equal(c.VTyp(0))
}

pub fn force_unsolved_hole_test() {
  // Force on unsolved hole returns the hole
  c.force(c.ffi_build, [], vhole(0)) |> should.equal(vhole(0))
}

pub fn force_solved_hole_test() {
  // Force on solved hole returns the solution
  let sub = [#(0, v32t)]
  c.force(c.ffi_build, sub, vhole(0)) |> should.equal(v32t)
}

// ============================================================================
// FORCE WITH SPINE
// ============================================================================

pub fn force_hole_with_spine_test() {
  // Force on solved hole with spine applies the spine
  let sub = [#(0, c.VLam([], "x", [], c.Var(0, s1)))]
  let v = c.VNeut(c.HHole(0), [c.EApp(v32t)])
  c.force(c.ffi_build, sub, v) |> should.equal(v32t)
}

// ============================================================================
// NESTED FORCE
// ============================================================================

pub fn force_nested_hole_test() {
  // Force recursively resolves nested holes
  let sub = [#(0, vhole(1)), #(1, v32t)]
  c.force(c.ffi_build, sub, vhole(0)) |> should.equal(v32t)
}
