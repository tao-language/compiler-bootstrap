/// Unit tests for the check function with Bool, Option, and Vec types
///
/// These tests verify that the GADT type system works correctly by checking
/// terms against expected types and verifying that type inference and
/// unification produce the correct results.
import core/ast.{
  type Value, type Term,
  VNeut, VCtr, VLit, VTyp, VTypeDef, Var,
  Int as LitInt, Float as LitFloat,
  IntT, FloatT, I32T, F64T, VLitT,
  VErr, HHole, HVar, EApp,
  Lit, Ctr, App, Lam, Pi, Ann, Match, Case,
  Rcd, RcdT, Typ, LitT, TypeDef, Fix,
  Hole,
}
import core/state.{initial_state, type State}
import core/infer.{check, infer, lookup_constructor, find_type_def}
import core/unify.{unify}
import gleam/list
import gleam/option.{Some, None}
import gleeunit
import syntax/span.{single}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Helper Functions
// ============================================================================

fn v_neut(level: Int) -> Value {
  VNeut(HVar(level), [])
}

fn v_lit_int(v: Int) -> Value {
  VLit(LitInt(v))
}

fn v_lit_float(v: Float) -> Value {
  VLit(LitFloat(v))
}

fn t_var(level: Int) -> Term {
  Var(level, single("test", 0, 0))
}

fn make_bool_type_def() -> Value {
  let constructors = [
    #("True", #([], v_neut(0), t_var(0)), single("test", 0, 0)),
    #("False", #([], v_neut(0), t_var(0)), single("test", 0, 0)),
  ]
  VTypeDef(name: "Bool", params: [], constructors: constructors)
}

fn make_option_type_def() -> Value {
  let self_type = t_var(0)
  let constructors = [
    #("Some", #([], v_neut(0), self_type), single("test", 0, 0)),
    #("None", #([], v_neut(0), self_type), single("test", 0, 0)),
  ]
  VTypeDef(name: "Option", params: [#("a", v_neut(0))], constructors: constructors)
}

fn make_list_type_def() -> Value {
  let self_type = t_var(0)
  let constructors = [
    #("Cons", #([], v_neut(0), self_type), single("test", 0, 0)),
    #("Nil", #([], v_neut(0), self_type), single("test", 0, 0)),
  ]
  VTypeDef(name: "List", params: [#("a", v_neut(0))], constructors: constructors)
}

// ============================================================================
// check Tests - Bool Type
// ============================================================================

pub fn check_bool_true_test() {
  // Check #True against #Bool
  let state = initial_state([])
  let term = Ctr("True", Lit(LitInt(0), single("", 0, 0)), single("", 0, 0))
  let expected = VCtr("Bool", v_neut(0))
  let #(value, type_, _) = check(state, term, expected)
  // Should succeed - True is a valid Bool constructor
  assert type_ != VErr
}

pub fn check_bool_false_test() {
  // Check #False against #Bool
  let state = initial_state([])
  let term = Ctr("False", Lit(LitInt(0), single("", 0, 0)), single("", 0, 0))
  let expected = VCtr("Bool", v_neut(0))
  let #(value, type_, _) = check(state, term, expected)
  // Should succeed - False is a valid Bool constructor
  assert type_ != VErr
}

pub fn check_bool_wrong_constructor_test() {
  // Check #Wrong against #Bool - should fail
  let state = initial_state([])
  let term = Ctr("Wrong", Lit(LitInt(0), single("", 0, 0)), single("", 0, 0))
  let expected = VCtr("Bool", v_neut(0))
  let #(value, type_, new_state) = check(state, term, expected)
  // Should fail - Wrong is not a valid Bool constructor
  assert value == VErr || list.length(new_state.errors) >= 1
}

// ============================================================================
// check Tests - Option Type
// ============================================================================

pub fn check_option_some_test() {
  // Check #Some(42) against #Option($Int)
  let state = initial_state([])
  let term = Ctr("Some", Ctr("Int", Lit(LitInt(42), single("", 0, 0)), single("", 0, 0)), single("", 0, 0))
  let expected = VCtr("Option", VLitT(IntT))
  let #(value, type_, _) = check(state, term, expected)
  // Should succeed - Some is a valid Option constructor
  assert type_ != VErr
}

pub fn check_option_none_test() {
  // Check #None against #Option($Int)
  let state = initial_state([])
  let term = Ctr("None", Lit(LitInt(0), single("", 0, 0)), single("", 0, 0))
  let expected = VCtr("Option", VLitT(IntT))
  let #(value, type_, _) = check(state, term, expected)
  // Should succeed - None is a valid Option constructor
  assert type_ != VErr
}

pub fn check_option_wrong_constructor_test() {
  // Check #Wrong against #Option($Int) - should fail
  let state = initial_state([])
  let term = Ctr("Wrong", Lit(LitInt(0), single("", 0, 0)), single("", 0, 0))
  let expected = VCtr("Option", VLitT(IntT))
  let #(value, type_, new_state) = check(state, term, expected)
  // Should fail - Wrong is not a valid Option constructor
  assert value == VErr || list.length(new_state.errors) >= 1
}

// ============================================================================
// check Tests - List Type
// ============================================================================

pub fn check_list_cons_test() {
  // Check #Cons against #List($Int)
  let state = initial_state([])
  let term = Ctr("Cons", Ctr("Int", Lit(LitInt(42), single("", 0, 0)), single("", 0, 0)), single("", 0, 0))
  let expected = VCtr("List", VLitT(IntT))
  let #(value, type_, _) = check(state, term, expected)
  // Should succeed - Cons is a valid List constructor
  assert type_ != VErr
}

pub fn check_list_nil_test() {
  // Check #Nil against #List($Int)
  let state = initial_state([])
  let term = Ctr("Nil", Lit(LitInt(0), single("", 0, 0)), single("", 0, 0))
  let expected = VCtr("List", VLitT(IntT))
  let #(value, type_, _) = check(state, term, expected)
  // Should succeed - Nil is a valid List constructor
  assert type_ != VErr
}

pub fn check_list_wrong_constructor_test() {
  // Check #Wrong against #List($Int) - should fail
  let state = initial_state([])
  let term = Ctr("Wrong", Lit(LitInt(0), single("", 0, 0)), single("", 0, 0))
  let expected = VCtr("List", VLitT(IntT))
  let #(value, type_, new_state) = check(state, term, expected)
  // Should fail - Wrong is not a valid List constructor
  assert value == VErr || list.length(new_state.errors) >= 1
}

// ============================================================================
// find_type_def Tests
// ============================================================================

pub fn find_type_def_bool_found_test() {
  // find_type_def should find Bool TypeDef when looking up #True
  let type_def = make_bool_type_def()
  let env = [type_def]
  let value = VCtr("True", v_neut(0))
  let result = find_type_def(env, value)
  assert case result {
    Some(#(td, _)) -> td == type_def
    None -> False
  }
}

pub fn find_type_def_option_found_test() {
  // find_type_def should find Option TypeDef when looking up #Some
  let type_def = make_option_type_def()
  let env = [type_def]
  let value = VCtr("Some", v_neut(0))
  let result = find_type_def(env, value)
  assert case result {
    Some(#(td, _)) -> td == type_def
    None -> False
  }
}

pub fn find_type_def_not_found_test() {
  // find_type_def should return None for unknown constructors
  let type_def = make_bool_type_def()
  let env = [type_def]
  let value = VCtr("Unknown", v_neut(0))
  let result = find_type_def(env, value)
  assert result == None
}

pub fn find_type_def_non_ctr_test() {
  // find_type_def should return None for non-VCtr values
  let type_def = make_bool_type_def()
  let env = [type_def]
  let value = VLit(LitInt(42))
  let result = find_type_def(env, value)
  assert result == None
}

// ============================================================================
// lookup_constructor Tests
// ============================================================================

pub fn lookup_constructor_bool_true_test() {
  // lookup_constructor should find True constructor in Bool TypeDef
  let type_def = make_bool_type_def()
  let env = [type_def]
  let result = lookup_constructor(env, "True")
  assert case result {
    Some(#(_, _, _)) -> True
    None -> False
  }
}

pub fn lookup_constructor_bool_false_test() {
  // lookup_constructor should find False constructor in Bool TypeDef
  let type_def = make_bool_type_def()
  let env = [type_def]
  let result = lookup_constructor(env, "False")
  assert case result {
    Some(#(_, _, _)) -> True
    None -> False
  }
}

pub fn lookup_constructor_option_some_test() {
  // lookup_constructor should find Some constructor in Option TypeDef
  let type_def = make_option_type_def()
  let env = [type_def]
  let result = lookup_constructor(env, "Some")
  assert case result {
    Some(#(_, _, _)) -> True
    None -> False
  }
}

pub fn lookup_constructor_not_found_test() {
  // lookup_constructor should return None for unknown constructors
  let type_def = make_bool_type_def()
  let env = [type_def]
  let result = lookup_constructor(env, "Unknown")
  assert result == None
}
