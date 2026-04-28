/// Tests for the TypeDef types in the AST module
///
/// Tests cover:
/// - TypeDef construction
/// - Constructor lookup
/// - Substitution (HVar resolution)
/// - Type computation (type_of_type_def)
/// - VType value construction

import core/ast.{
  ConstructorDef,
  TypeDef,
  type TypeDef,
  type Value,
  VNeut,
  VType,
  VPi,
  VCtr,
  VLit,
  HVar,
  HHole,
  VRcd,
  EApp,
  Int as LitInt,
  find_constructor,
  compute_constructor_type,
  subst,
  type_of_type_def,
  value_to_string,
}
import gleam/list
import gleam/option.{Some, None}
import gleeunit
import syntax/span.{single}

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

// ============================================================================
// TYPEDEF CONSTRUCTION TESTS
// ============================================================================

/// TypeDef with correct name.
pub fn type_def_name_test() {
  let td = TypeDef(
    name: "Option",
    param_count: 1,
    constructors: [
      ConstructorDef(tag: "Some", result_template: v_neut(0)),
      ConstructorDef(tag: "None", result_template: v_neut(0)),
    ],
  )
  assert td.name == "Option"
}

/// TypeDef with correct param_count.
pub fn type_def_param_count_test() {
  let td = TypeDef(
    name: "Option",
    param_count: 1,
    constructors: [ConstructorDef(tag: "Some", result_template: v_neut(0))],
  )
  assert td.param_count == 1
}

/// TypeDef with multiple constructors.
pub fn type_def_multiple_constructors_test() {
  let td = TypeDef(
    name: "Bool",
    param_count: 0,
    constructors: [
      ConstructorDef(tag: "True", result_template: v_neut(0)),
      ConstructorDef(tag: "False", result_template: v_neut(0)),
    ],
  )
  assert list.length(td.constructors) == 2
}

// ============================================================================
// CONSTRUCTOR LOOKUP TESTS
// ============================================================================

/// Find existing constructor by tag.
pub fn find_constructor_exists_test() {
  let td = TypeDef(
    name: "Option",
    param_count: 1,
    constructors: [ConstructorDef(tag: "Some", result_template: v_neut(0))],
  )
  let result = find_constructor(td, "Some")
  assert case result {
    Some(_) -> True
    None -> False
  }
}

/// Constructor not found returns None.
pub fn find_constructor_not_found_test() {
  let td = TypeDef(
    name: "Option",
    param_count: 1,
    constructors: [ConstructorDef(tag: "Some", result_template: v_neut(0))],
  )
  let result = find_constructor(td, "None")
  assert case result {
    Some(_) -> False
    None -> True
  }
}

/// Find constructor in multi-constructor TypeDef.
pub fn find_constructor_bool_test() {
  let td = TypeDef(
    name: "Bool",
    param_count: 0,
    constructors: [
      ConstructorDef(tag: "True", result_template: v_neut(0)),
      ConstructorDef(tag: "False", result_template: v_neut(0)),
    ],
  )
  let some = find_constructor(td, "True")
  let none = find_constructor(td, "False")
  assert case some {
    Some(_) -> True
    None -> False
  }
  assert case none {
    Some(_) -> True
    None -> False
  }
}

/// Find constructor in empty TypeDef.
pub fn find_constructor_empty_test() {
  let td = TypeDef(
    name: "Void",
    param_count: 0,
    constructors: [],
  )
  let result = find_constructor(td, "Any")
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
  let result = subst(args, template)
  // Substitution wraps in VNeut with EApp spine
  assert case result {
    VNeut(HVar(0), [EApp(VLit(LitInt(42)))]) -> True
    _ -> False
  }
}

/// Substitute HVar(1) with a value (second argument).
pub fn subst_hvar_one_test() {
  let template = VNeut(HVar(1), [])
  let args = [v_lit_int(1), v_lit_int(2)]
  let result = subst(args, template)
  assert case result {
    VNeut(HVar(0), [EApp(VLit(LitInt(2)))]) -> True
    _ -> False
  }
}

/// Substitute HVar(0) in a VCtr — wraps inner value in VNeut with EApp spine.
pub fn subst_in_ctr_test() {
  let template = VCtr("Pair", VNeut(HVar(0), []))
  let args = [v_lit_int(42)]
  let result = subst(args, template)
  assert case result {
    VCtr("Pair", VNeut(HVar(0), [EApp(VLit(LitInt(42)))])) -> True
    _ -> False
  }
}

/// Substitute HVar in nested VCtr.
pub fn subst_nested_ctr_test() {
  let template = VCtr("Outer", VCtr("Inner", VNeut(HVar(0), [])))
  let args = [v_lit_int(99)]
  let result = subst(args, template)
  assert case result {
    VCtr("Outer", VCtr("Inner", VNeut(HVar(0), [EApp(VLit(LitInt(99)))]))) -> True
    _ -> False
  }
}

/// HVar beyond args returns unchanged.
pub fn subst_hvar_beyond_args_test() {
  let template = VNeut(HVar(5), [])
  let args = [v_lit_int(42)]
  let result = subst(args, template)
  assert result == template
}

/// HHole is not substituted.
pub fn subst_hhole_test() {
  let template = VNeut(HHole(42), [])
  let args = [v_lit_int(42)]
  let result = subst(args, template)
  assert result == template
}

/// Substitute in VRcd — wraps each substituted value in VNeut with EApp spine.
pub fn subst_in_rcd_test() {
  let template = VRcd([#("x", VNeut(HVar(0), [])), #("y", v_lit_int(0))])
  let args = [v_lit_int(10)]
  let result = subst(args, template)
  assert case result {
    VRcd([#("x", VNeut(HVar(0), [EApp(VLit(LitInt(10)))])), #("y", VLit(LitInt(0)))]) -> True
    _ -> False
  }
}

// ============================================================================
// CONSTRUCTOR TYPE COMPUTATION TESTS
// ============================================================================

/// Compute type of constructor with param substitution.
pub fn compute_constructor_type_option_some_test() {
  let td = TypeDef(
    name: "Option",
    param_count: 1,
    constructors: [
      ConstructorDef(
        tag: "Some",
        result_template: VCtr("Option", VNeut(HVar(0), [])),
      ),
      ConstructorDef(
        tag: "None",
        result_template: VCtr("Option", VNeut(HVar(0), [])),
      ),
    ],
  )
  let result = compute_constructor_type(td, [v_lit_int(42)], "Some")
  let expected = VCtr("Option", VNeut(HVar(0), [EApp(v_lit_int(42))]))
  assert case result {
    Some(v) -> v == expected
    None -> False
  }
}

/// Constructor type not found returns None.
pub fn compute_constructor_type_not_found_test() {
  let td = TypeDef(
    name: "Option",
    param_count: 1,
    constructors: [ConstructorDef(tag: "Some", result_template: v_neut(0))],
  )
  let result = compute_constructor_type(td, [v_lit_int(42)], "None")
  assert case result {
    Some(_) -> False
    None -> True
  }
}

// ============================================================================
// TYPE OF TYPEDEF TESTS
// ============================================================================

/// type_of_type_def returns a Pi type with VType.
pub fn type_of_type_def_returns_pi_test() {
  let td = TypeDef(
    name: "Option",
    param_count: 1,
    constructors: [ConstructorDef(tag: "Some", result_template: v_neut(0))],
  )
  let result = type_of_type_def(td)
  assert case result {
    VPi(_, _, _, VPi(_, _, _, VType(t))) if t.name == "Option" -> True
    _ -> False
  }
}

// ============================================================================
// VTYPE VALUE TESTS
// ============================================================================

/// VType wraps a TypeDef.
pub fn vtype_wraps_type_def_test() {
  let td = TypeDef(
    name: "Bool",
    param_count: 0,
    constructors: [
      ConstructorDef(tag: "True", result_template: v_neut(0)),
      ConstructorDef(tag: "False", result_template: v_neut(0)),
    ],
  )
  let v = VType(td)
  assert case v {
    VType(t) if t.name == "Bool" -> True
    _ -> False
  }
}

/// VType in env lookup.
pub fn vtype_in_env_test() {
  let td = TypeDef(
    name: "Int",
    param_count: 0,
    constructors: [],
  )
  let v = VType(td)
  let str = value_to_string(v)
  assert str == "<type Int>"
}
