/// Tests for the Exhaustiveness module
///
/// Tests cover:
/// - Basic exhaustiveness checking for ADTs (Bool, Option, Nat)
/// - Missing pattern detection
/// - Redundant pattern detection
/// - TypeDef construction and extraction

import core/ast.{type ConstructorDef, type TypeDef}
import core/exhaustiveness.{
  check_exhaustiveness,
  extract_tags,
  is_redundant,
  make_type_def,
}
import core/state.{type State, type Error, MatchMissing, initial_state}
import gleam/list
import gleam/option.{Some, None}
import gleam/string
import gleeunit
import syntax/span.{single, type Span}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPERS
// ============================================================================

fn sp() -> Span {
  single("exhaustiveness_test", 0, 0)
}

fn make_state() -> State {
  initial_state([])
}

/// Extract constructor from Result(ConstructorDef, Nil).
fn unwrap_ctor(res: Result(ConstructorDef, Nil)) -> ConstructorDef {
  case res {
    Ok(c) -> c
    Error(_) -> panic
  }
}

/// Get the first element from a list of errors.
fn first_error(errors: List(Error)) -> Error {
  case list.first(errors) {
    Ok(e) -> e
    Error(_) -> panic
  }
}

// ============================================================================
// EXHAUSTIVENESS CHECKING TESTS
// ============================================================================

/// All constructors covered — no errors.
pub fn check_exhaustiveness_all_covered_bool_test() {
  let state = make_state()
  let td = make_type_def("Bool", ["True", "False"])
  let c0 = td.constructors |> list.first |> unwrap_ctor
  let c1 = td.constructors |> list.drop(1) |> list.first |> unwrap_ctor
  let constructors = [
    #("True", c0),
    #("False", c1),
  ]
  let covered = ["True", "False"]
  let result_state = check_exhaustiveness(state, constructors, covered, sp())
  assert result_state.errors == []
}

/// Missing one constructor — error reported.
pub fn check_exhaustiveness_missing_constructor_test() {
  let state = make_state()
  let td = make_type_def("Bool", ["True", "False"])
  let c0 = td.constructors |> list.first |> unwrap_ctor
  let c1 = td.constructors |> list.drop(1) |> list.first |> unwrap_ctor
  let constructors = [
    #("True", c0),
    #("False", c1),
  ]
  let covered = ["True"]
  let result_state = check_exhaustiveness(state, constructors, covered, sp())
  assert list.length(result_state.errors) == 1
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) if missing == ["False"] -> True
    _ -> False
  }
}

/// Missing both constructors — error with both listed.
pub fn check_exhaustiveness_none_covered_test() {
  let state = make_state()
  let td = make_type_def("Bool", ["True", "False"])
  let c0 = td.constructors |> list.first |> unwrap_ctor
  let c1 = td.constructors |> list.drop(1) |> list.first |> unwrap_ctor
  let constructors = [
    #("True", c0),
    #("False", c1),
  ]
  let covered = []
  let result_state = check_exhaustiveness(state, constructors, covered, sp())
  assert list.length(result_state.errors) == 1
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) -> list.sort(missing, string.compare) == ["False", "True"]
    _ -> False
  }
}

/// Option type with partial coverage.
pub fn check_exhaustiveness_option_partial_test() {
  let state = make_state()
  let td = make_type_def("Option", ["Some", "None"])
  let c0 = td.constructors |> list.first |> unwrap_ctor
  let c1 = td.constructors |> list.drop(1) |> list.first |> unwrap_ctor
  let constructors = [
    #("Some", c0),
    #("None", c1),
  ]
  let covered = ["Some"]
  let result_state = check_exhaustiveness(state, constructors, covered, sp())
  assert list.length(result_state.errors) == 1
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) if missing == ["None"] -> True
    _ -> False
  }
}

/// Nat type with Z covered, S missing.
pub fn check_exhaustiveness_nat_partial_test() {
  let state = make_state()
  let td = make_type_def("Nat", ["Z", "S"])
  let c0 = td.constructors |> list.first |> unwrap_ctor
  let c1 = td.constructors |> list.drop(1) |> list.first |> unwrap_ctor
  let constructors = [
    #("Z", c0),
    #("S", c1),
  ]
  let covered = ["Z"]
  let result_state = check_exhaustiveness(state, constructors, covered, sp())
  assert list.length(result_state.errors) == 1
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) if missing == ["S"] -> True
    _ -> False
  }
}

/// Three-way ADT with two out of three covered.
pub fn check_exhaustiveness_three_way_partial_test() {
  let state = make_state()
  let td = make_type_def("Tri", ["Red", "Green", "Blue"])
  let c0 = td.constructors |> list.first |> unwrap_ctor
  let c1 = td.constructors |> list.drop(1) |> list.first |> unwrap_ctor
  let c2 = td.constructors |> list.drop(2) |> list.first |> unwrap_ctor
  let constructors = [
    #("Red", c0),
    #("Green", c1),
    #("Blue", c2),
  ]
  let covered = ["Red", "Green"]
  let result_state = check_exhaustiveness(state, constructors, covered, sp())
  assert list.length(result_state.errors) == 1
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) -> list.sort(missing, string.compare) == ["Blue"]
    _ -> False
  }
}

// ============================================================================
// REDUNDANCY CHECKING TESTS
// ============================================================================

/// Pattern matching an already covered tag is redundant.
pub fn is_redundant_true_test() {
  assert is_redundant(["True", "False"], "True") == True
}

/// Pattern matching an un-covered tag is not redundant.
pub fn is_redundant_false_test() {
  assert is_redundant(["True", "False"], "True") == True
  assert is_redundant(["True", "False"], "Bottom") == False
}

/// Empty covered set — nothing is redundant.
pub fn is_redundant_empty_covered_test() {
  assert is_redundant([], "Any") == False
}

// ============================================================================
// TYPEDEF EXTRACTION TESTS
// ============================================================================

/// Extract tags from a TypeDef in correct order.
pub fn extract_tags_bool_test() {
  let td = make_type_def("Bool", ["True", "False"])
  let tags = extract_tags(td)
  assert tags == ["True", "False"]
}

/// Extract tags from Option type.
pub fn extract_tags_option_test() {
  let td = make_type_def("Option", ["Some", "None"])
  let tags = extract_tags(td)
  assert tags == ["Some", "None"]
}

/// Extract tags from Nat type.
pub fn extract_tags_nat_test() {
  let td = make_type_def("Nat", ["Z", "S"])
  let tags = extract_tags(td)
  assert tags == ["Z", "S"]
}

/// Extract tags from empty type (no constructors).
pub fn extract_tags_empty_test() {
  let td = make_type_def("Void", [])
  let tags = extract_tags(td)
  assert tags == []
}

/// Extract tags from three-way type.
pub fn extract_tags_tri_test() {
  let td = make_type_def("Tri", ["A", "B", "C"])
  let tags = extract_tags(td)
  assert tags == ["A", "B", "C"]
}

// ============================================================================
// TYPEDEF CONSTRUCTION TESTS
// ============================================================================

/// TypeDef has correct name.
pub fn make_type_def_name_test() {
  let td = make_type_def("MyType", ["X", "Y"])
  assert td.name == "MyType"
}

/// TypeDef has correct param_count (always 0 for now).
pub fn make_type_def_param_count_test() {
  let td = make_type_def("MyType", ["X", "Y"])
  assert td.param_count == 0
}

/// TypeDef has correct number of constructors.
pub fn make_type_def_constructor_count_test() {
  let td = make_type_def("MyType", ["X", "Y", "Z"])
  assert list.length(td.constructors) == 3
}

/// Each constructor has a tag.
pub fn make_type_def_constructor_tags_test() {
  let td = make_type_def("Colors", ["Red", "Green", "Blue"])
  let tags = list.map(td.constructors, fn(c) { c.tag })
  assert tags == ["Red", "Green", "Blue"]
}

// ============================================================================
// PROPERTY: EXHAUSTIVENESS COMPLETENESS
// ============================================================================

/// Full coverage always succeeds — property test.
pub fn check_exhaustiveness_full_coverage_property_test() {
  let type_pairs = [
    #("Bool", ["True", "False"]),
    #("Option", ["Some", "None"]),
    #("Nat", ["Z", "S"]),
    #("Tri", ["Red", "Green", "Blue"]),
    #("Void", []),
  ]

  let states = list.map(type_pairs, fn(pair) {
    let name = pair.0
    let constructors = pair.1
    let td = make_type_def(name, constructors)
    let full_covered = td.constructors |> list.map(fn(c) { c.tag })
    let state = make_state()
    let typed_constructors = td.constructors |> list.map(fn(c) { #("temp", c) })
    check_exhaustiveness(state, typed_constructors, full_covered, sp())
    state.errors == []
  })

  assert states |> list.all(fn(b) { b }) == True
}
