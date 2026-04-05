// ============================================================================
// HOLE FRESHNESS TESTS
// ============================================================================
/// Tests to verify that holes are correctly freshened during annotation processing.
///
/// The InfiniteType bug occurs when the same hole ID appears in multiple
/// places in type structures, causing unification cycles.
///
/// These tests verify that:
/// 1. freshen_annotation replaces negative holes with fresh positive IDs
/// 2. Each freshen_annotation call is independent
import gleeunit
import gleeunit/should
import core/ast.{Hole, Pi, Lam, Ctr, Unit, Rcd}
import core/infer.{freshen_annotation}
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Helper: Extract hole ID from a term
// ============================================================================

fn get_hole_id(term) -> Int {
  case term {
    Hole(id, _) -> id
    _ -> -9999  // Sentinel for non-hole terms
  }
}

fn get_pi_domain_hole_id(term) -> Int {
  case term {
    Pi(_, _, domain, _, _) -> get_hole_id(domain)
    _ -> -9999
  }
}

// ============================================================================
// TEST: freshen_annotation replaces negative holes with fresh IDs
// ============================================================================

pub fn freshen_single_negative_hole_test() {
  let span = Span("test", 0, 0, 0, 0)
  let term = Hole(-1, span)

  let #(fresh_term, counter) = freshen_annotation(term, 0)

  get_hole_id(fresh_term) |> should.equal(0)
  counter |> should.equal(1)
}

pub fn freshen_multiple_negative_holes_test() {
  let span = Span("test", 0, 0, 0, 0)
  let term1 = Hole(-1, span)
  let term2 = Hole(-5, span)

  let #(fresh1, c1) = freshen_annotation(term1, 0)
  let #(fresh2, c2) = freshen_annotation(term2, c1)

  get_hole_id(fresh1) |> should.equal(0)
  get_hole_id(fresh2) |> should.equal(1)
  c2 |> should.equal(2)
}

// ============================================================================
// TEST: freshen_annotation preserves non-negative holes
// ============================================================================

pub fn freshen_preserves_non_negative_holes_test() {
  let span = Span("test", 0, 0, 0, 0)
  let term = Hole(5, span)

  let #(fresh_term, counter) = freshen_annotation(term, 0)

  get_hole_id(fresh_term) |> should.equal(5)  // Preserved
  counter |> should.equal(0)  // Counter not incremented
}

// ============================================================================
// TEST: freshen_annotation handles Pi types
// ============================================================================

pub fn freshen_pi_with_negative_holes_test() {
  let span = Span("test", 0, 0, 0, 0)
  // Pi("_", Hole(-1), Hole(-2))
  let term = Pi([], "_", Hole(-1, span), Hole(-2, span), span)

  let #(fresh_term, counter) = freshen_annotation(term, 0)

  get_pi_domain_hole_id(fresh_term) |> should.equal(0)
  // Codomain should also be freshened
  case fresh_term {
    Pi(_, _, _, codomain, _) -> {
      get_hole_id(codomain) |> should.equal(1)
    }
    _ -> True |> should.be_true
  }
  counter |> should.equal(2)
}

pub fn freshen_nested_pi_test() {
  let span = Span("test", 0, 0, 0, 0)
  // Pi("_", Hole(-1), Pi("_", Hole(-1), Hole(-1)))
  let inner = Pi([], "_", Hole(-1, span), Hole(-1, span), span)
  let outer = Pi([], "_", Hole(-1, span), inner, span)

  let #(fresh_outer, counter) = freshen_annotation(outer, 0)

  // Outer domain: Hole(-1) → Hole(0)
  get_pi_domain_hole_id(fresh_outer) |> should.equal(0)

  // Inner domain: Hole(-1) → Hole(1)
  case fresh_outer {
    Pi(_, _, _, Pi(_, _, inner_dom, _, _), _) -> {
      get_hole_id(inner_dom) |> should.equal(1)
    }
    _ -> True |> should.be_true
  }

  counter |> should.equal(3)  // Three holes freshened
}

// ============================================================================
// TEST: freshen_annotation handles Lam types
// ============================================================================

pub fn freshen_lam_param_type_test() {
  let span = Span("test", 0, 0, 0, 0)
  // Lam([], #("x", Hole(-1)), Hole(-1))
  let term = Lam([], #("x", Hole(-1, span)), Hole(-1, span), span)

  let #(fresh_term, counter) = freshen_annotation(term, 0)

  case fresh_term {
    Lam(_, #(_, param_ty), body, _) -> {
      get_hole_id(param_ty) |> should.equal(0)
      get_hole_id(body) |> should.equal(1)
    }
    _ -> True |> should.be_true
  }
  counter |> should.equal(2)
}

// ============================================================================
// TEST: freshen_annotation handles Ctr and Rcd
// ============================================================================

pub fn freshen_ctr_arg_test() {
  let span = Span("test", 0, 0, 0, 0)
  let term = Ctr("Some", Hole(-1, span), span)

  let #(fresh_term, counter) = freshen_annotation(term, 0)

  case fresh_term {
    Ctr(_, arg, _) -> {
      get_hole_id(arg) |> should.equal(0)
    }
    _ -> True |> should.be_true
  }
  counter |> should.equal(1)
}

pub fn freshen_rcd_fields_test() {
  let span = Span("test", 0, 0, 0, 0)
  let term = Rcd([#("x", Hole(-1, span)), #("y", Hole(-2, span))], span)

  let #(fresh_term, counter) = freshen_annotation(term, 0)

  case fresh_term {
    Rcd(fields, _) -> {
      case fields {
        [ #("x", fx), #("y", fy) ] -> {
          get_hole_id(fx) |> should.equal(0)
          get_hole_id(fy) |> should.equal(1)
        }
        _ -> True |> should.be_true
      }
    }
    _ -> True |> should.be_true
  }
  counter |> should.equal(2)
}

// ============================================================================
// TEST: Each freshen call starts with independent counter
// ============================================================================

pub fn independent_freshening_test() {
  let span = Span("test", 0, 0, 0, 0)
  let term1 = Hole(-1, span)
  let term2 = Hole(-1, span)

  // Freshen both starting from 0 — they get the SAME IDs
  // This is intentional: freshening is per-annotation, not global
  let #(fresh1, _) = freshen_annotation(term1, 0)
  let #(fresh2, _) = freshen_annotation(term2, 0)

  get_hole_id(fresh1) |> should.equal(0)
  get_hole_id(fresh2) |> should.equal(0)  // Same ID, but in different annotations
}

// ============================================================================
// TEST: Deeply nested structures
// ============================================================================

pub fn freshen_deeply_nested_test() {
  let span = Span("test", 0, 0, 0, 0)

  // Build: Pi(H(-1), Pi(H(-1), Pi(H(-1), Pi(H(-1), H(-1)))))
  let inner = Pi([], "_", Hole(-1, span), Hole(-1, span), span)
  let inner2 = Pi([], "_", Hole(-1, span), inner, span)
  let inner3 = Pi([], "_", Hole(-1, span), inner2, span)
  let outer = Pi([], "_", Hole(-1, span), inner3, span)

  let #(fresh_term, counter) = freshen_annotation(outer, 0)

  // Should have freshened 5 holes (4 domain + 1 final)
  counter |> should.equal(5)
}

// ============================================================================
// TEST: Same hole ID in different parts of structure gets different fresh IDs
// ============================================================================

pub fn same_hole_id_different_fresh_ids_test() {
  let span = Span("test", 0, 0, 0, 0)
  // Pi("_", Hole(-1), Pi("_", Hole(-1), Hole(-1)))
  // All three Hole(-1) should get DIFFERENT fresh IDs
  let inner = Pi([], "_", Hole(-1, span), Hole(-1, span), span)
  let outer = Pi([], "_", Hole(-1, span), inner, span)

  let #(fresh_outer, _) = freshen_annotation(outer, 0)

  case fresh_outer {
    Pi(_, _, outer_dom, Pi(_, _, inner_dom, inner_cod, _), _) -> {
      let outer_id = get_hole_id(outer_dom)
      let inner_dom_id = get_hole_id(inner_dom)
      let inner_cod_id = get_hole_id(inner_cod)

      // All three should be different
      outer_id |> should.not_equal(inner_dom_id)
      outer_id |> should.not_equal(inner_cod_id)
      inner_dom_id |> should.not_equal(inner_cod_id)
    }
    _ -> True |> should.be_true
  }
}
