import gleeunit
import core/ast.{Var, Hole, Lam, App, Pi, Lit, Ctr, Typ, PAny, PVar, PCtr, PUnit, VNeut, HVar, HHole, VLam, VPi, VLit, VCtr, VUnit, VErr, Err as AstErr, Unit as AstUnit, Int as LitInt, Float as LitFloat, make_neut, make_hole_neut, make_var_neut, error_term, shift_term, term_to_string, value_to_string}
import syntax/span.{single}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Literal constructors
// ============================================================================

pub fn create_integer_literal_test() {
  let l = LitInt(42)
  assert l == LitInt(42)
}

pub fn create_float_literal_test() {
  let l = LitFloat(3.14)
  assert l == LitFloat(3.14)
}

// ============================================================================
// Term constructors
// ============================================================================

pub fn create_variable_test() {
  let t = Var(0, single("test.gleam", 1, 1))
  assert t == Var(0, single("test.gleam", 1, 1))
}

pub fn create_hole_test() {
  let t = Hole(1, single("test.gleam", 1, 1))
  assert t == Hole(1, single("test.gleam", 1, 1))
}

pub fn create_lambda_test() {
  let body = Var(0, single("test.gleam", 1, 2))
  let lam = Lam(#("x", Hole(-1, single("test.gleam", 1, 1))), body, single("test.gleam", 1, 3))
  assert lam == Lam(#("x", Hole(-1, single("test.gleam", 1, 1))), Var(0, single("test.gleam", 1, 2)), single("test.gleam", 1, 3))
}

pub fn create_application_test() {
  let fun = Var(0, single("test.gleam", 1, 1))
  let arg = Lit(LitInt(42), single("test.gleam", 1, 3))
  let app = App(fun, arg, single("test.gleam", 1, 5))
  assert app == App(Var(0, single("test.gleam", 1, 1)), Lit(LitInt(42), single("test.gleam", 1, 3)), single("test.gleam", 1, 5))
}

pub fn create_pi_type_test() {
  let domain = Var(0, single("test.gleam", 1, 1))
  let codomain = Var(1, single("test.gleam", 1, 3))
  let pi = Pi(domain, codomain, single("test.gleam", 1, 5))
  assert pi == Pi(Var(0, single("test.gleam", 1, 1)), Var(1, single("test.gleam", 1, 3)), single("test.gleam", 1, 5))
}

pub fn create_literal_term_test() {
  let t = Lit(LitInt(42), single("test.gleam", 1, 1))
  assert t == Lit(LitInt(42), single("test.gleam", 1, 1))
}

pub fn create_constructor_test() {
  let t = Ctr("Some", Var(0, single("test.gleam", 1, 1)), single("test.gleam", 1, 5))
  assert t == Ctr("Some", Var(0, single("test.gleam", 1, 1)), single("test.gleam", 1, 5))
}

pub fn create_unit_test() {
  let t = AstUnit(single("test.gleam", 1, 1))
  assert t == AstUnit(single("test.gleam", 1, 1))
}

pub fn create_type_test() {
  let t = Typ(single("test.gleam", 1, 1))
  assert t == Typ(single("test.gleam", 1, 1))
}

pub fn create_error_term_test() {
  let t = AstErr("oops", single("test.gleam", 1, 1))
  assert t == AstErr("oops", single("test.gleam", 1, 1))
}

pub fn error_term_helper_creates_error_test() {
  let t = error_term("test error", single("test.gleam", 1, 1))
  assert t == AstErr("test error", single("test.gleam", 1, 1))
}

// ============================================================================
// Pattern constructors
// ============================================================================

pub fn create_pany_pattern_test() {
  let p = PAny(single("test.gleam", 1, 1))
  assert p == PAny(single("test.gleam", 1, 1))
}

pub fn create_pvar_pattern_test() {
  let p = PVar("x", single("test.gleam", 1, 1))
  assert p == PVar("x", single("test.gleam", 1, 1))
}

pub fn create_pctr_pattern_test() {
  let p = PCtr("Cons", PVar("hd", single("test.gleam", 1, 1)), single("test.gleam", 1, 5))
  assert p == PCtr("Cons", PVar("hd", single("test.gleam", 1, 1)), single("test.gleam", 1, 5))
}

pub fn create_punit_pattern_test() {
  let p = PUnit(single("test.gleam", 1, 1))
  assert p == PUnit(single("test.gleam", 1, 1))
}

// ============================================================================
// Value constructors
// ============================================================================

pub fn create_neut_value_test() {
  let v = VNeut(HVar(0), [])
  assert v == VNeut(HVar(0), [])
}

pub fn create_hole_neut_value_test() {
  let v = VNeut(HHole(1), [])
  assert v == VNeut(HHole(1), [])
}

pub fn create_lambda_value_test() {
  let body = Var(0, single("test.gleam", 1, 1))
  let v = VLam(#("x", body), body)
  assert v == VLam(#("x", Var(0, single("test.gleam", 1, 1))), Var(0, single("test.gleam", 1, 1)))
}

pub fn create_pi_value_test() {
  let dom = VNeut(HVar(0), [])
  let codom = VNeut(HVar(1), [])
  let v = VPi(dom, codom)
  assert v == VPi(VNeut(HVar(0), []), VNeut(HVar(1), []))
}

pub fn create_literal_value_test() {
  let v = VLit(LitInt(42))
  assert v == VLit(LitInt(42))
}

pub fn create_constructor_value_test() {
  let v = VCtr("Just", VNeut(HVar(0), []))
  assert v == VCtr("Just", VNeut(HVar(0), []))
}

pub fn create_unit_value_test() {
  let v = VUnit
  assert v == VUnit
}

pub fn create_error_value_test() {
  let v = VErr
  assert v == VErr
}

// ============================================================================
// Helper functions
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
// Shift operations
// ============================================================================

pub fn shift_term_positive_on_free_variable_test() {
  let t = Var(2, single("test.gleam", 1, 1))
  let shifted = shift_term(t, 1)
  assert shifted == Var(3, single("test.gleam", 1, 1))
}

pub fn shift_term_negative_on_free_variable_test() {
  let t = Var(2, single("test.gleam", 1, 1))
  let shifted = shift_term(t, -1)
  assert shifted == Var(1, single("test.gleam", 1, 1))
}

pub fn shift_term_does_not_affect_bound_variable_test() {
  let body = Var(0, single("test.gleam", 1, 1))
  let lam = Lam(#("x", body), Var(0, single("test.gleam", 1, 2)), single("test.gleam", 1, 3))
  let shifted = shift_term(lam, 1)
  assert shifted == Lam(#("x", Var(1, single("test.gleam", 1, 1))), Var(0, single("test.gleam", 1, 2)), single("test.gleam", 1, 3))
}

pub fn shift_term_on_hole_is_no_op_test() {
  let t = Hole(5, single("test.gleam", 1, 1))
  let shifted = shift_term(t, 10)
  assert shifted == Hole(5, single("test.gleam", 1, 1))
}

pub fn shift_term_on_literal_is_no_op_test() {
  let t = Lit(LitInt(42), single("test.gleam", 1, 1))
  let shifted = shift_term(t, 10)
  assert shifted == Lit(LitInt(42), single("test.gleam", 1, 1))
}

// ============================================================================
// String representation
// ============================================================================

pub fn term_to_string_variable_test() {
  let t = Var(2, single("test.gleam", 1, 1))
  assert term_to_string(t) == "#2"
}

pub fn term_to_string_hole_test() {
  let t = Hole(5, single("test.gleam", 1, 1))
  assert term_to_string(t) == "?5"
}

pub fn term_to_string_lambda_test() {
  let body = Var(0, single("test.gleam", 1, 2))
  let t = Lam(#("x", Hole(-1, single("test.gleam", 1, 1))), body, single("test.gleam", 1, 3))
  assert term_to_string(t) == "λx.#0"
}

pub fn term_to_string_application_test() {
  let t = App(
    Var(0, single("test.gleam", 1, 1)),
    Lit(LitInt(42), single("test.gleam", 1, 3)),
    single("test.gleam", 1, 5),
  )
  assert term_to_string(t) == "(#0 42)"
}

pub fn term_to_string_integer_literal_test() {
  let t = Lit(LitInt(42), single("test.gleam", 1, 1))
  assert term_to_string(t) == "42"
}

pub fn term_to_string_unit_test() {
  let t = AstUnit(single("test.gleam", 1, 1))
  assert term_to_string(t) == "()"
}

pub fn term_to_string_type_test() {
  let t = Typ(single("test.gleam", 1, 1))
  assert term_to_string(t) == "Type"
}

// ============================================================================
// Value string representation
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
  let body = Var(0, single("test.gleam", 1, 1))
  let v = VLam(#("x", body), body)
  assert value_to_string(v) == "λx.#0"
}

pub fn value_to_string_integer_literal_test() {
  let v = VLit(LitInt(42))
  assert value_to_string(v) == "42"
}

pub fn value_to_string_unit_test() {
  let v = VUnit
  assert value_to_string(v) == "()"
}

pub fn value_to_string_error_test() {
  let v = VErr
  assert value_to_string(v) == "<error>"
}
