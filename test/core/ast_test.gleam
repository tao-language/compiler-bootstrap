import gleeunit
import gleam/list
import core/ast.{Var, Hole, Lam, App, Pi, Lit, Ctr, Ann, Match, Case, Typ, PAny, PVar, PCtr, PUnit, PLit, VNeut, HVar, HHole, VLam, VPi, VLit, VCtr, VRcd, Rcd, VErr, Err, Int as LitInt, Float as LitFloat, make_neut, make_hole_neut, make_var_neut, error_term, shift_term, term_to_string, value_to_string, EApp}
import gleam/option.{None}
import syntax/span.{single}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Term constructors - verify field values are correctly stored
// ============================================================================

pub fn term_variable_stores_index_and_span_test() {
  let t = Var(42, single("file.gleam", 10, 5))
  assert t.index == 42
  assert t.span.start_line == 10
  assert t.span.start_col == 5
}

pub fn term_hole_stores_id_and_span_test() {
  let t = Hole(-1, single("file.gleam", 1, 1))
  assert t.id == -1
  assert t.span.file == "file.gleam"
}

pub fn term_lambda_stores_name_body_and_span_test() {
  let body = Var(0, single("file.gleam", 1, 2))
  let param_type = Hole(-1, single("file.gleam", 1, 1))
  let t = Lam(#("x", param_type, body), body, single("file.gleam", 1, 3))
  assert case t {
    Lam(#(name, _, _), _, _) -> name == "x"
  }
}

pub fn term_application_stores_fun_arg_and_span_test() {
  let t = App(Var(0, single("file.gleam", 1, 1)), Lit(LitInt(42), single("file.gleam", 1, 3)), single("file.gleam", 1, 5))
  assert case t {
    App(Var(index, _), arg, _) -> index == 0 && arg == Lit(LitInt(42), single("file.gleam", 1, 3))
    _ -> False
  }
}

pub fn term_pi_stores_domain_codomain_and_span_test() {
  let t = Pi(Var(0, single("file.gleam", 1, 1)), Var(1, single("file.gleam", 1, 3)), single("file.gleam", 1, 5))
  assert case t {
    Pi(Var(domain_index, _), Var(codomain_index, _), _) -> domain_index == 0 && codomain_index == 1
    _ -> False
  }
}

pub fn term_literal_stores_literal_and_span_test() {
  let t = Lit(LitInt(42), single("file.gleam", 1, 1))
  assert t.value == LitInt(42)
}

pub fn term_constructor_stores_tag_arg_and_span_test() {
  let t = Ctr("Some", Var(0, single("file.gleam", 1, 1)), single("file.gleam", 1, 5))
  assert t.tag == "Some"
  assert t.arg == Var(0, single("file.gleam", 1, 1))
}

pub fn term_unit_stores_span_test() {
  assert Rcd([], single("file.gleam", 1, 1)) == Rcd([], single("file.gleam", 1, 1))
}

pub fn term_type_stores_span_test() {
  let t = Typ(0, single("file.gleam", 1, 1))
  assert t.span.start_col == 1
}

pub fn term_error_stores_message_and_span_test() {
  let t = Err("oops", single("file.gleam", 1, 1))
  assert t.message == "oops"
  assert t.span.file == "file.gleam"
}

pub fn error_term_helper_creates_ast_error_test() {
  let t = error_term("test error", single("file.gleam", 1, 1))
  assert t == Err("test error", single("file.gleam", 1, 1))
}

// ============================================================================
// Pattern constructors - verify field values are correctly stored
// ============================================================================

pub fn pattern_any_stores_span_test() {
  let p = PAny(single("file.gleam", 1, 1))
  assert p.span.start_line == 1
}

pub fn pattern_var_stores_name_and_span_test() {
  let p = PVar("x", single("file.gleam", 1, 1))
  assert p.name == "x"
}

pub fn pattern_ctr_stores_tag_arg_and_span_test() {
  let p = PCtr("Cons", PVar("hd", single("file.gleam", 1, 1)), single("file.gleam", 1, 5))
  assert p.tag == "Cons"
}

pub fn pattern_unit_stores_span_test() {
  let p = PUnit(single("file.gleam", 1, 1))
  assert p.span.start_col == 1
}

// ============================================================================
// Value constructors - verify field values are correctly stored
// ============================================================================

pub fn neut_value_stores_head_and_spine_test() {
  let v = VNeut(HVar(0), [])
  assert v.head == HVar(0)
  assert v.spine == []
}

pub fn neut_value_stores_hole_head_test() {
  let v = VNeut(HHole(5), [EApp(VRcd([]))])
  assert v.head == HHole(5)
  assert list.length(v.spine) == 1
}

pub fn lam_value_stores_param_and_body_test() {
  let body = Var(0, single("file.gleam", 1, 1))
  let param_type = Hole(-1, single("file.gleam", 1, 1))
  let v = VLam(#("x", param_type, body), body)
  assert case v {
    VLam(#(name, _, _), _) -> name == "x"
  }
}

pub fn pi_value_stores_domain_and_codomain_test() {
  let dom = VNeut(HVar(0), [])
  let codom = VNeut(HVar(1), [])
  let v = VPi(dom, codom)
  assert v.domain == dom
  assert v.codomain == codom
}

pub fn lit_value_stores_literal_test() {
  let v = VLit(LitInt(42))
  assert v.value == LitInt(42)
}

pub fn ctr_value_stores_tag_and_arg_test() {
  let v = VCtr("Just", VNeut(HVar(0), []))
  assert v.tag == "Just"
}

// ============================================================================
// Helper functions - verify they produce correct structures
// ============================================================================

pub fn make_neut_creates_neutral_with_empty_spine_test() {
  let v = make_neut(HVar(0))
  assert v == VNeut(HVar(0), [])
}

pub fn make_hole_neut_creates_neutral_from_hole_id_test() {
  let v = make_hole_neut(5)
  assert v == VNeut(HHole(5), [])
}

pub fn make_var_neut_creates_neutral_from_level_test() {
  let v = make_var_neut(3)
  assert v == VNeut(HVar(3), [])
}

// ============================================================================
// Shift operations - verify actual transformations
// ============================================================================

pub fn shift_term_positive_on_free_variable_increments_index_test() {
  let t = Var(2, single("file.gleam", 1, 1))
  let shifted = shift_term(t, 1)
  assert shifted == Var(3, single("file.gleam", 1, 1))
}

pub fn shift_term_negative_on_free_variable_decrements_index_test() {
  let t = Var(2, single("file.gleam", 1, 1))
  let shifted = shift_term(t, -1)
  assert shifted == Var(1, single("file.gleam", 1, 1))
}

pub fn shift_term_on_bound_variable_increments_index_test() {
  let body = Var(0, single("file.gleam", 1, 1))
  let param_type = Hole(-1, single("file.gleam", 1, 1))
  let lam = Lam(#("x", param_type, body), Var(0, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
  let shifted = shift_term(lam, 1)
  assert shifted == Lam(#("x", Var(1, single("file.gleam", 1, 1)), Var(0, single("file.gleam", 1, 1))), Var(0, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
}

pub fn shift_term_on_hole_is_no_op_test() {
  let t = Hole(5, single("file.gleam", 1, 1))
  let shifted = shift_term(t, 10)
  assert shifted == Hole(5, single("file.gleam", 1, 1))
}

pub fn shift_term_on_literal_is_no_op_test() {
  let t = Lit(LitInt(42), single("file.gleam", 1, 1))
  let shifted = shift_term(t, 10)
  assert shifted == Lit(LitInt(42), single("file.gleam", 1, 1))
}

pub fn shift_term_on_app_shifts_both_parts_test() {
  let app = App(Var(2, single("file.gleam", 1, 1)), Var(3, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
  let shifted = shift_term(app, 1)
  assert shifted == App(Var(3, single("file.gleam", 1, 1)), Var(4, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
}

pub fn shift_term_on_match_shifts_arg_and_cases_test() {
  let body = Var(0, single("file.gleam", 1, 1))
  let case_expr = Case(PAny(single("file.gleam", 1, 1)), None, body, single("file.gleam", 1, 2))
  let match_expr = Match(Var(0, single("file.gleam", 1, 3)), [case_expr], single("file.gleam", 1, 4))
  let shifted = shift_term(match_expr, 1)
  assert shifted == Match(
    Var(1, single("file.gleam", 1, 3)),
    [Case(PAny(single("file.gleam", 1, 1)), None, Var(1, single("file.gleam", 1, 1)), single("file.gleam", 1, 2))],
    single("file.gleam", 1, 4),
  )
}

pub fn shift_term_on_let_shifts_value_and_body_test() {
  let body = Var(0, single("file.gleam", 1, 1))
  let value = Var(2, single("file.gleam", 1, 2))
  let param_type = Rcd([], single("file.gleam", 1, 3))
  let let_expr = App(Lam(#("x", param_type, body), body, single("file.gleam", 1, 3)), value, single("file.gleam", 1, 3))
  let shifted = shift_term(let_expr, 1)
  // value is shifted with from=0: Var(2) -> Var(3)
  // body is shifted with from=1: Var(0) stays Var(0) (bound by Lam)
  let expected = App(Lam(#("x", param_type, Var(0, single("file.gleam", 1, 1))), Var(0, single("file.gleam", 1, 1)), single("file.gleam", 1, 3)), Var(3, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
  assert shifted == expected
}

pub fn shift_term_on_ann_shifts_term_and_type_test() {
  let ann = Ann(Var(2, single("file.gleam", 1, 1)), Var(3, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
  let shifted = shift_term(ann, 1)
  assert shifted == Ann(Var(3, single("file.gleam", 1, 1)), Var(4, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
}

pub fn shift_term_on_ctr_shifts_arg_test() {
  let ctr = Ctr("Cons", Var(2, single("file.gleam", 1, 1)), single("file.gleam", 1, 2))
  let shifted = shift_term(ctr, 1)
  assert shifted == Ctr("Cons", Var(3, single("file.gleam", 1, 1)), single("file.gleam", 1, 2))
}

pub fn shift_term_negative_on_all_vars_decrements_indices_test() {
  // Shift -1 should decrease all vars by 1 (since from=0 by default)
  let body = Var(0, single("file.gleam", 1, 1))
  let param_type = Hole(-1, single("file.gleam", 1, 1))
  let outer = Var(1, single("file.gleam", 1, 2))
  let lam = Lam(#("x", param_type, body), outer, single("file.gleam", 1, 3))
  let shifted = shift_term(lam, -1)
  // Var(1) becomes Var(0), and Var(0) becomes Var(-1)
  assert shifted == Lam(#("x", Var(-1, single("file.gleam", 1, 1)), Var(0, single("file.gleam", 1, 1))), Var(0, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
}

pub fn shift_term_on_pi_shifts_domain_and_codomain_test() {
  let pi = Pi(Var(2, single("file.gleam", 1, 1)), Var(3, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
  let shifted = shift_term(pi, 1)
  assert shifted == Pi(Var(3, single("file.gleam", 1, 1)), Var(4, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
}

pub fn shift_term_zero_does_nothing_test() {
  let t = Var(5, single("file.gleam", 1, 1))
  let shifted = shift_term(t, 0)
  assert shifted == Var(5, single("file.gleam", 1, 1))
}

pub fn shift_term_preserves_span_through_shifts_test() {
  let span = single("file.gleam", 5, 10)
  let t = Var(2, span)
  let shifted = shift_term(t, 1)
  assert case shifted {
    Var(_, s) -> s.start_line == 5 && s.start_col == 10
    _ -> False
  }
}

// ============================================================================
// String representation - verify actual output matches expectations
// ============================================================================

pub fn term_to_string_variable_test() {
  let t = Var(2, single("file.gleam", 1, 1))
  assert term_to_string(t) == "#2"
}

pub fn term_to_string_hole_test() {
  let t = Hole(5, single("file.gleam", 1, 1))
  assert term_to_string(t) == "?5"
}

pub fn term_to_string_lambda_test() {
  let body = Var(0, single("file.gleam", 1, 2))
  let param_type = Hole(-1, single("file.gleam", 1, 1))
  let t = Lam(#("x", param_type, body), body, single("file.gleam", 1, 3))
  assert term_to_string(t) == "%fn(x: ?-1) => #0"
}

pub fn term_to_string_application_test() {
  let t = App(
    Var(0, single("file.gleam", 1, 1)),
    Lit(LitInt(42), single("file.gleam", 1, 3)),
    single("file.gleam", 1, 5),
  )
  assert term_to_string(t) == "fun(#0: 42)"
}

pub fn term_to_string_integer_literal_test() {
  let t = Lit(LitInt(42), single("file.gleam", 1, 1))
  assert term_to_string(t) == "42"
}

pub fn term_to_string_float_literal_test() {
  let t = Lit(LitFloat(3.14), single("file.gleam", 1, 1))
  assert term_to_string(t) == "3.14"
}

pub fn term_to_string_unit_test() {
  let t = Rcd([], single("file.gleam", 1, 1))
  assert term_to_string(t) == "()"
}

pub fn term_to_string_type_test() {
  let t = Typ(0, single("file.gleam", 1, 1))
  assert term_to_string(t) == "%Type(0)"
}

pub fn term_to_string_error_test() {
  let t = Err("error", single("file.gleam", 1, 1))
  assert term_to_string(t) == "\"error\""
}

// ============================================================================
// Value string representation - verify actual output matches expectations
// ============================================================================

pub fn value_to_string_neut_variable_test() {
  let v = VNeut(HVar(0), [])
  assert value_to_string(v) == "v0"
}

pub fn value_to_string_neut_hole_test() {
  let v = VNeut(HHole(5), [])
  assert value_to_string(v) == "?5"
}

pub fn value_to_string_lambda_test() {
  let body = Var(0, single("file.gleam", 1, 1))
  let param_type = Hole(-1, single("file.gleam", 1, 1))
  let v = VLam(#("x", param_type, body), body)
  assert value_to_string(v) == "%fn(x) => #0"
}

pub fn value_to_string_integer_literal_test() {
  let v = VLit(LitInt(42))
  assert value_to_string(v) == "42"
}

pub fn value_to_string_float_literal_test() {
  let v = VLit(LitFloat(3.14))
  assert value_to_string(v) == "3.14"
}

pub fn value_to_string_unit_test() {
  let v = VRcd([])
  assert value_to_string(v) == "()"
}

pub fn value_to_string_error_test() {
  let v = VErr
  assert value_to_string(v) == "<error>"
}

// ============================================================================
// Additional shift_term edge case tests
// ============================================================================

pub fn shift_term_nested_lam_shifts_correctly_test() {
  // Nested lambdas: λx.(λy.0) shifted by 1 should correctly adjust param free vars
  let inner_body = Var(0, single("file.gleam", 1, 1))
  let inner_param = Hole(-1, single("file.gleam", 1, 1))
  let inner_lam = Lam(#("y", inner_param, inner_body), inner_body, single("file.gleam", 1, 1))
  let outer_param = Hole(-1, single("file.gleam", 1, 1))
  let outer_lam = Lam(#("x", outer_param, inner_lam), inner_lam, single("file.gleam", 1, 1))
  let shifted = shift_term(outer_lam, 1)
  // Param (inner_lam) shifted with from=0:
  //   inner param: Var(0) -> Var(1) (free var in param body)
  //   inner body: Var(0) stays Var(0) (bound by inner lam, shifted with from=1)
  // Body (inner_lam) shifted with from=1:
  //   inner param: Var(0) stays Var(0) (free var >= 1 not present here)
  //   inner body: Var(0) stays Var(0) (bound by inner lam, from=2)
  assert shifted == Lam(
    #("x", outer_param, Lam(#("y", Var(1, single("file.gleam", 1, 1)), Var(0, single("file.gleam", 1, 1))), Var(0, single("file.gleam", 1, 1)), single("file.gleam", 1, 1))),
    Lam(#("y", Var(0, single("file.gleam", 1, 1)), Var(0, single("file.gleam", 1, 1))), Var(0, single("file.gleam", 1, 1)), single("file.gleam", 1, 1)),
    single("file.gleam", 1, 1),
  )
}

pub fn shift_term_on_ann_preserves_span_test() {
  // shift_term on Ann should preserve spans
  let ann = Ann(Var(2, single("file.gleam", 1, 1)), Var(3, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
  let shifted = shift_term(ann, 1)
  assert case shifted {
    Ann(_, type_: Var(_, span: type_span), span: main_span) ->
      type_span.start_line == 1 && type_span.start_col == 2
      && main_span.start_line == 1 && main_span.start_col == 3
    _ -> False
  }
}

pub fn shift_term_on_match_preserves_case_bodies_span_test() {
  // shift_term on Match should preserve spans in case bodies
  let body = Var(0, single("file.gleam", 1, 1))
  let case_expr = Case(PAny(single("file.gleam", 1, 1)), None, body, single("file.gleam", 1, 2))
  let match_expr = Match(Var(0, single("file.gleam", 1, 3)), [case_expr], single("file.gleam", 1, 4))
  let shifted = shift_term(match_expr, 1)
  assert shifted == Match(
    Var(1, single("file.gleam", 1, 3)),
    [Case(PAny(single("file.gleam", 1, 1)), None, Var(1, single("file.gleam", 1, 1)), single("file.gleam", 1, 2))],
    single("file.gleam", 1, 4),
  )
}

pub fn shift_term_preserves_span_test() {
  // shift_term should preserve spans, not just adjust indices
  let t = Var(0, single("file.gleam", 5, 10))
  let shifted = shift_term(t, 5)
  assert case shifted {
    Var(index: 5, span: s) -> s.start_line == 5 && s.start_col == 10
    _ -> False
  }
}

pub fn shift_term_on_let_preserves_span_test() {
  // shift_term on App(Lam) should preserve spans
  let body = Var(0, single("file.gleam", 1, 1))
  let value = Var(2, single("file.gleam", 1, 2))
  let param_type = Rcd([], single("file.gleam", 1, 3))
  let let_expr = App(Lam(#("x", param_type, body), body, single("file.gleam", 1, 3)), value, single("file.gleam", 1, 3))
  let shifted = shift_term(let_expr, 1)
  assert case shifted {
    App(Lam(#(_, _, _body), body2, _lam_span), value, main_span) ->
      case value {
        Var(3, val_span) -> case body2 {
          Var(0, body_span) ->
            val_span.start_line == 1 && val_span.start_col == 2
            && body_span.start_line == 1 && body_span.start_col == 1
            && main_span.start_line == 1 && main_span.start_col == 3
          _ -> False
        }
        _ -> False
      }
    _ -> False
  }
}

// ============================================================================
// Missing string representation tests
//
// These tests verify term_to_string and value_to_string work correctly
// for all Term and Value constructors.
// ============================================================================

pub fn term_to_string_match_test() {
  // Match with a single case should format correctly
  let body = Var(0, single("file.gleam", 1, 1))
  let case_expr = Case(PAny(single("file.gleam", 1, 1)), None, body, single("file.gleam", 1, 2))
  let match_expr = Match(Var(0, single("file.gleam", 1, 3)), [case_expr], single("file.gleam", 1, 4))
  assert term_to_string(match_expr) == "%match #0 {\n  | _ => #0\n}"
}

pub fn term_to_string_let_test() {
  // App(Lam) should format as "fun(...)"
  let body = Var(0, single("file.gleam", 1, 1))
  let value = Lit(LitInt(42), single("file.gleam", 1, 2))
  let param_type = Rcd([], single("file.gleam", 1, 3))
  let let_expr = App(Lam(#("x", param_type, body), body, single("file.gleam", 1, 3)), value, single("file.gleam", 1, 3))
  assert term_to_string(let_expr) == "fun(%fn(x: ()) => #0: 42)"
}

pub fn term_to_string_ann_test() {
  // Ann should format as "<term>: <type>"
  let ann = Ann(Var(0, single("file.gleam", 1, 1)), Var(1, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
  assert term_to_string(ann) == "#0: #1"
}

pub fn term_to_string_ctr_test() {
  // Ctr without annotated arg should format as just the tag
  let ctr = Ctr("Some", Var(0, single("file.gleam", 1, 1)), single("file.gleam", 1, 2))
  assert term_to_string(ctr) == "#Some"
}

pub fn value_to_string_ctr_test() {
  // VCtr should format as "tag(<arg>)"
  let v = VCtr("Just", VNeut(HVar(0), []))
  assert value_to_string(v) == "Just(v0)"
}

pub fn value_to_string_pi_test() {
  // VPi should format as "Π<domain>.<codomain>"
  let dom = VNeut(HHole(0), [])
  let codom = VNeut(HVar(0), [])
  let v = VPi(dom, codom)
  assert value_to_string(v) == "Π?0.v0"
}

// ============================================================================
// Pattern string representation tests
// ============================================================================

pub fn pattern_to_string_var_test() {
  // PVar should format as the variable name
  let body = Var(0, single("file.gleam", 1, 1))
  let case_expr = Case(PVar("x", single("file.gleam", 1, 1)), None, body, single("file.gleam", 1, 2))
  let match_expr = Match(Var(0, single("file.gleam", 1, 3)), [case_expr], single("file.gleam", 1, 4))
  assert term_to_string(match_expr) == "%match #0 {\n  | x => #0\n}"
}

pub fn pattern_to_string_lit_int_test() {
  // PLit(Int) should format as the integer value
  let body = Var(0, single("file.gleam", 1, 1))
  let case_expr = Case(PLit(LitInt(0), single("file.gleam", 1, 1)), None, body, single("file.gleam", 1, 2))
  let match_expr = Match(Lit(LitInt(0), single("file.gleam", 1, 3)), [case_expr], single("file.gleam", 1, 4))
  assert term_to_string(match_expr) == "%match 0 {\n  | 0 => #0\n}"
}

pub fn pattern_to_string_lit_float_test() {
  // PLit(Float) should format as the float value
  let body = Var(0, single("file.gleam", 1, 1))
  let case_expr = Case(PLit(LitFloat(1.0), single("file.gleam", 1, 1)), None, body, single("file.gleam", 1, 2))
  let match_expr = Match(Lit(LitFloat(1.0), single("file.gleam", 1, 3)), [case_expr], single("file.gleam", 1, 4))
  assert term_to_string(match_expr) == "%match 1.0 {\n  | 1.0 => #0\n}"
}

// ============================================================================
// shift_term deeper edge cases
// ============================================================================

pub fn shift_term_on_ctr_nested_shifts_arg_test() {
  // shift_term on Ctr with nested Var should shift the argument
  let ctr = Ctr("Cons", Var(3, single("file.gleam", 1, 1)), single("file.gleam", 1, 2))
  let shifted = shift_term(ctr, 1)
  assert shifted == Ctr("Cons", Var(4, single("file.gleam", 1, 1)), single("file.gleam", 1, 2))
}

pub fn shift_term_on_ctr_zero_shift_preserves_test() {
  // shift_term with shift=0 should preserve everything
  let ctr = Ctr("Some", Var(5, single("file.gleam", 1, 1)), single("file.gleam", 1, 2))
  let shifted = shift_term(ctr, 0)
  assert shifted == ctr
}

pub fn shift_term_on_pi_both_shifted_test() {
  // shift_term on Pi should shift both domain and codomain
  let pi = Pi(Var(1, single("file.gleam", 1, 1)), Var(2, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
  let shifted = shift_term(pi, 1)
  assert shifted == Pi(Var(2, single("file.gleam", 1, 1)), Var(3, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
}

pub fn shift_term_on_ann_both_shifted_test() {
  // shift_term on Ann should shift both term and type
  let ann = Ann(Var(1, single("file.gleam", 1, 1)), Var(2, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
  let shifted = shift_term(ann, 1)
  assert shifted == Ann(Var(2, single("file.gleam", 1, 1)), Var(3, single("file.gleam", 1, 2)), single("file.gleam", 1, 3))
}

pub fn shift_term_on_match_multiple_cases_test() {
  // shift_term on Match with multiple cases should shift all case bodies
  let body1 = Var(1, single("file.gleam", 1, 1))
  let body2 = Var(2, single("file.gleam", 1, 2))
  let cases = [
    Case(PAny(single("file.gleam", 1, 1)), None, body1, single("file.gleam", 1, 3)),
    Case(PAny(single("file.gleam", 1, 2)), None, body2, single("file.gleam", 1, 4)),
  ]
  let match_expr = Match(Var(0, single("file.gleam", 1, 5)), cases, single("file.gleam", 1, 6))
  let shifted = shift_term(match_expr, 1)
  assert shifted == Match(
    Var(1, single("file.gleam", 1, 5)),
    [
      Case(PAny(single("file.gleam", 1, 1)), None, Var(2, single("file.gleam", 1, 1)), single("file.gleam", 1, 3)),
      Case(PAny(single("file.gleam", 1, 2)), None, Var(3, single("file.gleam", 1, 2)), single("file.gleam", 1, 4)),
    ],
    single("file.gleam", 1, 6),
  )
}

pub fn shift_term_negative_on_literal_preserves_test() {
  // Negative shift on literal should be no-op
  let t = Lit(LitInt(42), single("file.gleam", 1, 1))
  let shifted = shift_term(t, -5)
  assert shifted == t
}

pub fn shift_term_on_hole_preserves_id_test() {
  // shift_term on Hole should not change the ID
  let t = Hole(42, single("file.gleam", 1, 1))
  let shifted = shift_term(t, 10)
  assert shifted == Hole(42, single("file.gleam", 1, 1))
}

// ============================================================================
// Structural equality tests
// ============================================================================

pub fn term_equality_on_same_structure_test() {
  // Two structurally identical terms should be equal
  let t1 = Var(0, single("file.gleam", 1, 1))
  let t2 = Var(0, single("file.gleam", 1, 1))
  assert t1 == t2
}

pub fn term_inequality_on_different_index_test() {
  // Terms with different indices should not be equal
  let t1 = Var(0, single("file.gleam", 1, 1))
  let t2 = Var(1, single("file.gleam", 1, 1))
  assert t1 != t2
}

pub fn value_equality_on_same_structure_test() {
  // Two structurally identical values should be equal
  let v1 = VNeut(HVar(0), [])
  let v2 = VNeut(HVar(0), [])
  assert v1 == v2
}

pub fn value_inequality_on_different_head_test() {
  // Values with different heads should not be equal
  let v1 = VNeut(HVar(0), [])
  let v2 = VNeut(HHole(0), [])
  assert v1 != v2
}
