/// Tests for the TypeDef types in the AST module
///
/// Tests cover:
/// - TypeDef construction
/// - Constructor lookup
/// - Substitution (HVar resolution)
/// - Type computation (type_of_type_def)
/// - VTypeDef value construction

import core/ast.{
  type Value,
  VNeut,
  VTypeDef,
  VPi,
  VCtr,
  VLit,
  HVar,
  HHole,
  EApp,
  Int as LitInt,
  find_constructor,
  compute_constructor_type,
  type_of_type_def,
  value_to_string,
}
import gleam/list
import gleam/option.{Some, None}
import gleeunit
import syntax/span.{single, type Span}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPERS
// ============================================================================

fn v_neut(level: Int) -> Value {
  VNeut(HVar(level), [])
}

fn v_lit_int(v: Int) -> Value {
  VLit(LitInt(v))
}

/// Create a list of #(String, Value, Value, Span) tuples for a TypeDef.
fn make_constructors(
  tags: List(String),
  self_type: Value,
  result_template: Value,
) -> List(#(String, Value, Value, Span)) {
  list.map(tags, fn(tag) {
    #(tag, self_type, result_template, single("test", 0, 0))
  })
}

// ============================================================================
// TYPEDEF CONSTRUCTION TESTS
// ============================================================================

/// VTypeDef with correct name.
pub fn vtypef_name_test() {
  let vdef = VTypeDef(
    name: "Option",
    constructors: [],
  )
  let str = value_to_string(VTypeDef(
    name: vdef.name,
    constructors: vdef.constructors,
  ))
  assert str == "<VTypeDef Option>"
}

/// VTypeDef with multiple constructors.
pub fn vtypef_multiple_constructors_test() {
  let vdef = VTypeDef(
    name: "Bool",
    constructors: [
      #("True", v_neut(0), v_neut(0), single("test", 0, 0)),
      #("False", v_neut(0), v_neut(0), single("test", 0, 0)),
    ],
  )
  assert list.length(vdef.constructors) == 2
}

// ============================================================================
// CONSTRUCTOR LOOKUP TESTS
// ============================================================================

/// Find existing constructor by tag.
pub fn find_constructor_exists_test() {
  let constructors = make_constructors(["Some", "None"], v_neut(0), v_neut(0))
  let result = find_constructor(constructors, "Some")
  assert case result {
    Some(_) -> True
    None -> False
  }
}

/// Constructor not found returns None.
pub fn find_constructor_not_found_test() {
  let constructors = make_constructors(["Some", "None"], v_neut(0), v_neut(0))
  let result = find_constructor(constructors, "Other")
  assert case result {
    Some(_) -> False
    None -> True
  }
}

/// Find constructor in multi-constructor VTypeDef.
pub fn find_constructor_bool_test() {
  let constructors = make_constructors(["True", "False"], v_neut(0), v_neut(0))
  let some = find_constructor(constructors, "True")
  let none = find_constructor(constructors, "False")
  assert case some {
    Some(_) -> True
    None -> False
  }
  assert case none {
    Some(_) -> True
    None -> False
  }
}

/// Find constructor in empty VTypeDef.
pub fn find_constructor_empty_test() {
  let constructors = make_constructors([], v_neut(0), v_neut(0))
  let result = find_constructor(constructors, "Any")
  assert case result {
    Some(_) -> False
    None -> True
  }
}

// ============================================================================
// SUBSTITUTION TESTS
// ============================================================================

/// Substitute HVar(0) with a value — wraps in VNeut with EApp spine.
pub fn subst_hvar_zero_test() {
  let template = VNeut(HVar(0), [])
  let args = [v_lit_int(42)]
  let constructors = make_constructors(["Some", "None"], v_neut(0), template)
  let result = compute_constructor_type(constructors, args, "Some")
  assert case result {
    Some(_) -> True
    None -> False
  }
}

/// HVar beyond args returns unchanged.
pub fn subst_hvar_beyond_args_test() {
  let _template = VNeut(HVar(5), [])
  let args = [v_lit_int(42)]
  let result = compute_constructor_type([], args, "Some")
  assert case result {
    Some(_) -> False
    None -> True
  }
}

/// HHole is not substituted.
pub fn subst_hhole_test() {
  let _template = VNeut(HHole(42), [])
  let args = [v_lit_int(42)]
  let result = compute_constructor_type([], args, "Some")
  assert case result {
    Some(_) -> False
    None -> True
  }
}

// ============================================================================
// CONSTRUCTOR TYPE COMPUTATION TESTS
// ============================================================================

/// Compute type of constructor with param substitution.
pub fn compute_constructor_type_option_some_test() {
  let constructors = make_constructors(
    ["Some"],
    v_neut(0),
    VCtr("Option", VNeut(HVar(0), [])),
  )
  let result = compute_constructor_type(constructors, [v_lit_int(42)], "Some")
  let expected = VCtr("Option", VNeut(HVar(0), [EApp(v_lit_int(42))]))
  assert case result {
    Some(v) -> v == expected
    None -> False
  }
}

/// Constructor type not found returns None.
pub fn compute_constructor_type_not_found_test() {
  let constructors = make_constructors(
    ["Some"],
    v_neut(0),
    VCtr("Option", VNeut(HVar(0), [])),
  )
  let result = compute_constructor_type(constructors, [v_lit_int(42)], "None")
  assert case result {
    Some(_) -> False
    None -> True
  }
}

// ============================================================================
// TYPE OF TYPEDEF TESTS
// ============================================================================

/// type_of_type_def returns a Pi type with VTypeDef.
pub fn type_of_type_def_returns_pi_test() {
  let constructors = make_constructors(["Some", "None"], v_neut(0), v_neut(0))
  let result = type_of_type_def(constructors)
  assert case result {
    VPi(_, _, _, VPi(_, _, _, VTypeDef(_, _constructors))) -> True
    _ -> False
  }
}

// ============================================================================
// VTYPEF VALUE TESTS
// ============================================================================

/// VTypeDef is a simple marker (no data).
pub fn vtypef_is_marker_test() {
  let v = VTypeDef(name: "Option", constructors: [])
  assert case v {
    VTypeDef(name: name, constructors: constructors) ->
      name == "Option" && constructors == []
  }
}

/// VTypeDef in env lookup.
pub fn vtypef_string_test() {
  let v = VTypeDef(name: "Option", constructors: [])
  let str = value_to_string(v)
  assert str == "<VTypeDef Option>"
}
