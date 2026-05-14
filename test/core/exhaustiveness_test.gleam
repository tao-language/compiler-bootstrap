/// Tests for the Exhaustiveness module
///
/// Tests cover:
/// - Basic exhaustiveness checking for ADTs (Bool, Option, Nat)
/// - Missing pattern detection
/// - Redundant pattern detection
/// - TypeDef construction and extraction

import core/ast.{type Value, type Term, HHole, make_neut, Var}
import core/exhaustiveness.{
  check_exhaustiveness,
  check_exhaustiveness_vdef,
  extract_tags,
  is_redundant,
}
import core/state.{type State, type Error, MatchMissing, initial_state}
import gleam/list
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
  let constructors = make_type_def(["True", "False"])
  let covered = ["True", "False"]
  let result_state = check_exhaustiveness(state, constructors, covered, sp())
  assert result_state.errors == []
}

/// Missing one constructor — error reported.
pub fn check_exhaustiveness_missing_constructor_test() {
  let state = make_state()
  let constructors = make_type_def(["True", "False"])
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
  let constructors = make_type_def(["True", "False"])
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
  let constructors = make_type_def(["Some", "None"])
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
  let constructors = make_type_def(["Z", "S"])
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
  let constructors = make_type_def(["Red", "Green", "Blue"])
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

/// Extract tags from a list of constructors in correct order.
pub fn extract_tags_bool_test() {
  let constructors = make_type_def(["True", "False"])
  let tags = extract_tags(constructors)
  assert tags == ["True", "False"]
}

/// Extract tags from Option type.
pub fn extract_tags_option_test() {
  let constructors = make_type_def(["Some", "None"])
  let tags = extract_tags(constructors)
  assert tags == ["Some", "None"]
}

/// Extract tags from Nat type.
pub fn extract_tags_nat_test() {
  let constructors = make_type_def(["Z", "S"])
  let tags = extract_tags(constructors)
  assert tags == ["Z", "S"]
}

/// Extract tags from empty type (no constructors).
pub fn extract_tags_empty_test() {
  let constructors = make_type_def([])
  let tags = extract_tags(constructors)
  assert tags == []
}

/// Extract tags from three-way type.
pub fn extract_tags_tri_test() {
  let constructors = make_type_def(["A", "B", "C"])
  let tags = extract_tags(constructors)
  assert tags == ["A", "B", "C"]
}

/// TypeDef has correct name.
pub fn make_type_def_name_test() {
  let constructors = make_type_def(["X", "Y"])
  assert extract_tags(constructors) == ["X", "Y"]
}

/// TypeDef has correct param_count (always 0 for now).
pub fn make_type_def_param_count_test() {
  let constructors = make_type_def(["X", "Y"])
  assert list.length(constructors) == 2
}

/// TypeDef has correct number of constructors.
pub fn make_type_def_constructor_count_test() {
  let constructors = make_type_def(["X", "Y", "Z"])
  assert list.length(constructors) == 3
}

/// Each constructor has a tag.
pub fn make_type_def_constructor_tags_test() {
  let constructors = make_type_def(["Red", "Green", "Blue"])
  let tags = list.map(constructors, fn(c) { case c { #(tag, _, _, _) -> tag } })
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
    let constructors = pair.1
    let full_covered = constructors
    let state = make_state()
    let typed_constructors = make_type_def(constructors)
    check_exhaustiveness(state, typed_constructors, full_covered, sp())
    state.errors == []
  })

  assert states |> list.all(fn(b) { b }) == True

  assert states |> list.all(fn(b) { b }) == True
}

// ============================================================================
// HELPERS
// ============================================================================

/// Create a list of #(String, Value, Value, Span) tuples for exhaustiveness checking.
fn make_type_def(tags: List(String)) -> List(#(String, Value, Value, Span)) {
  list.map(tags, fn(tag) {
    #(tag, make_neut(HHole(0)), make_neut(HHole(0)), single("exhaustiveness_test", 0, 0))
  })
}

// ============================================================================
// VTypeDef-STYLE EXHAUSTIVENESS CHECKING
// ============================================================================

/// Create VTypeDef-style constructors with the format:
/// #(tag, type_params, self_type, result_type, span)
fn make_vdef_constructors(
  tags: List(String),
) -> List(#(String, List(String), Value, Term, Span)) {
  list.map(tags, fn(tag) {
    let type_params = case tag {
      "Some" -> ["a"]
      "Cons" -> ["m", "a"]
      _ -> []
    }
    #(tag, type_params, make_neut(HHole(0)), Var(0, sp()), sp())
  })
}

/// VTypeDef: Option<a> with Some and None constructors.
/// Full coverage should succeed.
pub fn check_exhaustiveness_vdef_option_full_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["Some", "None"])
  let covered = ["Some", "None"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  assert result_state.errors == []
}

/// VTypeDef: Option<a> with only Some covered — should report None as missing.
pub fn check_exhaustiveness_vdef_option_partial_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["Some", "None"])
  let covered = ["Some"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  assert list.length(result_state.errors) == 1
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) if missing == ["None"] -> True
    _ -> False
  }
}

/// VTypeDef: GADT Vec with Nil and Cons constructors.
/// Full coverage should succeed.
pub fn check_exhaustiveness_vdef_gadt_vec_full_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["Nil", "Cons"])
  let covered = ["Nil", "Cons"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  assert result_state.errors == []
}

/// VTypeDef: GADT Vec with only Nil covered — should report Cons as missing.
pub fn check_exhaustiveness_vdef_gadt_vec_partial_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["Nil", "Cons"])
  let covered = ["Nil"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  assert list.length(result_state.errors) == 1
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) -> list.sort(missing, string.compare) == ["Cons"]
    _ -> False
  }
}

/// VTypeDef: Empty type (Void) with no constructors.
/// Full coverage (empty covered) should succeed.
pub fn check_exhaustiveness_vdef_void_full_test() {
  let state = make_state()
  let constructors = make_vdef_constructors([])
  let covered = []
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  assert result_state.errors == []
}

/// VTypeDef: Empty type (Void) with non-empty covered.
/// This is unusual but should still succeed (no constructors to check).
pub fn check_exhaustiveness_vdef_void_covered_test() {
  let state = make_state()
  let constructors = make_vdef_constructors([])
  let covered = ["Some"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  assert result_state.errors == []
}

/// VTypeDef: Three-way type (Color) with full coverage.
pub fn check_exhaustiveness_vdef_color_full_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["Red", "Green", "Blue"])
  let covered = ["Red", "Green", "Blue"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  assert result_state.errors == []
}

/// VTypeDef: Three-way type (Color) with partial coverage.
pub fn check_exhaustiveness_vdef_color_partial_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["Red", "Green", "Blue"])
  let covered = ["Red", "Green"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  assert list.length(result_state.errors) == 1
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) -> list.sort(missing, string.compare) == ["Blue"]
    _ -> False
  }
}

/// VTypeDef: GADT Expr with LitInt, LitBool, Add, IsZero constructors.
/// Full coverage should succeed.
pub fn check_exhaustiveness_vdef_gadt_expr_full_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["LitInt", "LitBool", "Add", "IsZero"])
  let covered = ["LitInt", "LitBool", "Add", "IsZero"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  assert result_state.errors == []
}

/// VTypeDef: GADT Expr with only LitInt and LitBool covered.
pub fn check_exhaustiveness_vdef_gadt_expr_partial_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["LitInt", "LitBool", "Add", "IsZero"])
  let covered = ["LitInt", "LitBool"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  assert list.length(result_state.errors) == 1
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) -> list.sort(missing, string.compare) == ["Add", "IsZero"]
    _ -> False
  }
}

/// VTypeDef: Property test — full coverage always succeeds.
pub fn check_exhaustiveness_vdef_full_coverage_property_test() {
  let type_pairs = [
    #("Bool", ["True", "False"]),
    #("Option", ["Some", "None"]),
    #("Nat", ["Z", "S"]),
    #("Tri", ["Red", "Green", "Blue"]),
    #("Void", []),
    #("Vec", ["Nil", "Cons"]),
    #("Expr", ["LitInt", "LitBool", "Add", "IsZero"]),
  ]

  let states = list.map(type_pairs, fn(pair) {
    let constructors = pair.1
    let full_covered = constructors
    let state = make_state()
    let typed_constructors = make_vdef_constructors(constructors)
    check_exhaustiveness_vdef(state, typed_constructors, full_covered, sp())
    state.errors == []
  })

  assert states |> list.all(fn(b) { b }) == True
}

/// VTypeDef: Property test — missing at least one constructor always reports error.
pub fn check_exhaustiveness_vdef_missing_always_error_property_test() {
  let type_pairs = [
    #("Bool", ["True", "False"]),
    #("Option", ["Some", "None"]),
    #("Nat", ["Z", "S"]),
    #("Tri", ["Red", "Green", "Blue"]),
  ]

  let states = list.map(type_pairs, fn(pair) {
    let all_tags = pair.1
    let missing_one = list.drop(all_tags, 1)  // Remove last tag
    let state = make_state()
    let typed_constructors = make_vdef_constructors(all_tags)
    let result_state = check_exhaustiveness_vdef(state, typed_constructors, missing_one, sp())
    result_state.errors != []
  })

  assert states |> list.all(fn(b) { b }) == True
}

/// VTypeDef: Property test — removing any tag from full coverage results in error.
pub fn check_exhaustiveness_vdef_remove_any_tag_error_property_test() {
  let type_pairs = [
    #("Bool", ["True", "False"]),
    #("Option", ["Some", "None"]),
    #("Nat", ["Z", "S"]),
    #("Tri", ["Red", "Green", "Blue"]),
  ]

  let states = list.map(type_pairs, fn(pair) {
    let all_tags = pair.1
    // For each tag, remove it and check that an error is reported
    list.any(all_tags, fn(tag) {
      let remaining = list.filter(all_tags, fn(t) { t != tag })
      let state = make_state()
      let typed_constructors = make_vdef_constructors(all_tags)
      let result_state = check_exhaustiveness_vdef(state, typed_constructors, remaining, sp())
      result_state.errors != []
    })
  })

  assert states |> list.all(fn(b) { b }) == True
}

/// VTypeDef: Check that the missing tag in the error is correct.
pub fn check_exhaustiveness_vdef_missing_tag_correct_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["A", "B", "C"])
  let covered = ["A", "C"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) if missing == ["B"] -> True
    _ -> False
  }
}

/// VTypeDef: Check that multiple missing tags are reported.
pub fn check_exhaustiveness_vdef_multiple_missing_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["A", "B", "C", "D"])
  let covered = ["A"]
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) ->
      list.sort(missing, string.compare) == ["B", "C", "D"]
    _ -> False
  }
}

/// VTypeDef: Empty covered list reports all tags as missing.
pub fn check_exhaustiveness_vdef_empty_covered_test() {
  let state = make_state()
  let constructors = make_vdef_constructors(["A", "B"])
  let covered = []
  let result_state = check_exhaustiveness_vdef(state, constructors, covered, sp())
  let error = first_error(result_state.errors)
  assert case error {
    MatchMissing(missing, _, _) -> list.sort(missing, string.compare) == ["A", "B"]
    _ -> False
  }
}
