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
  case l {
    LitInt(42) -> True
    _ -> False
  }
}

pub fn create_float_literal_test() {
  let l = LitFloat(3.14)
  case l {
    LitFloat(3.14) -> True
    _ -> False
  }
}

// ============================================================================
// Term constructors
// ============================================================================

pub fn create_variable_test() {
  let t = Var(0, single("test.gleam", 1, 1))
  case t {
    Var(index, span) -> index == 0 && span.start_line == 1
  }
}

pub fn create_hole_test() {
  let t = Hole(1, single("test.gleam", 1, 1))
  case t {
    Hole(id, span) -> id == 1 && span.start_line == 1
  }
}

pub fn create_lambda_test() {
  let body = Var(0, single("test.gleam", 1, 2))
  let lam = Lam(#("x", Hole(-1, single("test.gleam", 1, 1))), body, single("test.gleam", 1, 3))
  case lam {
    Lam(#(name, _param), body, _span) ->
      name == "x" && body == Var(0, single("test.gleam", 1, 2))
  }
}

pub fn create_application_test() {
  let fun = Var(0, single("test.gleam", 1, 1))
  let arg = Lit(LitInt(42), single("test.gleam", 1, 3))
  let app = App(fun, arg, single("test.gleam", 1, 5))
  case app {
    App(f, a, _span) -> f == Var(0, single("test.gleam", 1, 1)) && a == Lit(LitInt(42), single("test.gleam", 1, 3))
  }
}

pub fn create_pi_type_test() {
  let domain = Var(0, single("test.gleam", 1, 1))
  let codomain = Var(1, single("test.gleam", 1, 3))
  let pi = Pi(domain, codomain, single("test.gleam", 1, 5))
  case pi {
    Pi(d, c, _span) -> d == domain && c == codomain
  }
}

pub fn create_literal_term_test() {
  let t = Lit(LitInt(42), single("test.gleam", 1, 1))
  case t {
    Lit(LitInt(42), span) -> span.start_line == 1
    _ -> False
  }
}

pub fn create_constructor_test() {
  let t = Ctr("Some", Var(0, single("test.gleam", 1, 1)), single("test.gleam", 1, 5))
  case t {
    Ctr("Some", _, _) -> True
    _ -> False
  }
}

pub fn create_unit_test() {
  let t = AstUnit(single("test.gleam", 1, 1))
  case t {
    AstUnit(span) -> span.start_line == 1
  }
}

pub fn create_type_test() {
  let t = Typ(single("test.gleam", 1, 1))
  case t {
    Typ(span) -> span.start_line == 1
  }
}

pub fn create_error_term_test() {
  let t = AstErr("oops", single("test.gleam", 1, 1))
  case t {
    AstErr(msg, span) -> msg == "oops" && span.start_line == 1
  }
}

pub fn error_term_helper_creates_error_test() {
  let t = error_term("test error", single("test.gleam", 1, 1))
  case t {
    AstErr("test error", _) -> True
    _ -> False
  }
}

// ============================================================================
// Pattern constructors
// ============================================================================

pub fn create_pany_pattern_test() {
  let p = PAny(single("test.gleam", 1, 1))
  case p {
    PAny(span) -> span.start_line == 1
  }
}

pub fn create_pvar_pattern_test() {
  let p = PVar("x", single("test.gleam", 1, 1))
  case p {
    PVar(name, span) -> name == "x" && span.start_line == 1
  }
}

pub fn create_pctr_pattern_test() {
  let p = PCtr("Cons", PVar("hd", single("test.gleam", 1, 1)), single("test.gleam", 1, 5))
  case p {
    PCtr(tag, _, _) -> tag == "Cons"
  }
}

pub fn create_punit_pattern_test() {
  let p = PUnit(single("test.gleam", 1, 1))
  case p {
    PUnit(span) -> span.start_line == 1
  }
}

// ============================================================================
// Value constructors
// ============================================================================

pub fn create_neut_value_test() {
  let v = VNeut(HVar(0), [])
  case v {
    VNeut(HVar(0), _) -> True
    _ -> False
  }
}

pub fn create_hole_neut_value_test() {
  let v = VNeut(HHole(1), [])
  case v {
    VNeut(HHole(1), _) -> True
    _ -> False
  }
}

pub fn create_lambda_value_test() {
  let body = Var(0, single("test.gleam", 1, 1))
  let v = VLam(#("x", body), body)
  case v {
    VLam(#("x", _), _) -> True
    _ -> False
  }
}

pub fn create_pi_value_test() {
  let dom = VNeut(HVar(0), [])
  let codom = VNeut(HVar(1), [])
  let v = VPi(dom, codom)
  case v {
    VPi(VNeut(HVar(0), _), VNeut(HVar(1), _)) -> True
    _ -> False
  }
}

pub fn create_literal_value_test() {
  let v = VLit(LitInt(42))
  case v {
    VLit(LitInt(42)) -> True
    _ -> False
  }
}

pub fn create_constructor_value_test() {
  let v = VCtr("Just", VNeut(HVar(0), []))
  case v {
    VCtr("Just", _) -> True
    _ -> False
  }
}

pub fn create_unit_value_test() {
  let v = VUnit
  case v {
    VUnit -> True
    _ -> False
  }
}

pub fn create_error_value_test() {
  let v = VErr
  case v {
    VErr -> True
    _ -> False
  }
}

// ============================================================================
// Helper functions
// ============================================================================

pub fn make_neut_creates_neutral_with_empty_spine_test() {
  let v = make_neut(HVar(0))
  case v {
    VNeut(HVar(0), []) -> True
    _ -> False
  }
}

pub fn make_hole_neut_creates_neutral_from_hole_id_test() {
  let v = make_hole_neut(5)
  case v {
    VNeut(HHole(5), _) -> True
    _ -> False
  }
}

pub fn make_var_neut_creates_neutral_from_level_test() {
  let v = make_var_neut(3)
  case v {
    VNeut(HVar(3), _) -> True
    _ -> False
  }
}

// ============================================================================
// Shift operations
// ============================================================================

pub fn shift_term_positive_on_free_variable_test() {
  let t = Var(2, single("test.gleam", 1, 1))
  let shifted = shift_term(t, 1)
  case shifted {
    Var(3, _) -> True
    _ -> False
  }
}

pub fn shift_term_negative_on_free_variable_test() {
  let t = Var(2, single("test.gleam", 1, 1))
  let shifted = shift_term(t, -1)
  case shifted {
    Var(1, _) -> True
    _ -> False
  }
}

pub fn shift_term_does_not_affect_bound_variable_test() {
  let body = Var(0, single("test.gleam", 1, 1))
  let lam = Lam(#("x", body), Var(0, single("test.gleam", 1, 2)), single("test.gleam", 1, 3))
  let shifted = shift_term(lam, 1)
  case shifted {
    Lam(#(_, param), _body, _) ->
      case param {
        Var(0, _) -> True  // Bound var stays at 0
        _ -> False
      }
    _ -> False
  }
}

pub fn shift_term_on_hole_is_no_op_test() {
  let t = Hole(5, single("test.gleam", 1, 1))
  let shifted = shift_term(t, 10)
  case shifted {
    Hole(5, _) -> True
    _ -> False
  }
}

pub fn shift_term_on_literal_is_no_op_test() {
  let t = Lit(LitInt(42), single("test.gleam", 1, 1))
  let shifted = shift_term(t, 10)
  case shifted {
    Lit(LitInt(42), _) -> True
    _ -> False
  }
}

// ============================================================================
// String representation
// ============================================================================

pub fn term_to_string_variable_test() {
  let t = Var(2, single("test.gleam", 1, 1))
  term_to_string(t) == "#2"
}

pub fn term_to_string_hole_test() {
  let t = Hole(5, single("test.gleam", 1, 1))
  term_to_string(t) == "?5"
}

pub fn term_to_string_lambda_test() {
  let body = Var(0, single("test.gleam", 1, 2))
  let t = Lam(#("x", Hole(-1, single("test.gleam", 1, 1))), body, single("test.gleam", 1, 3))
  term_to_string(t) == "λx.?(-1)"
}

pub fn term_to_string_application_test() {
  let t = App(
    Var(0, single("test.gleam", 1, 1)),
    Lit(LitInt(42), single("test.gleam", 1, 3)),
    single("test.gleam", 1, 5),
  )
  term_to_string(t) == "(#0 42)"
}

pub fn term_to_string_integer_literal_test() {
  let t = Lit(LitInt(42), single("test.gleam", 1, 1))
  term_to_string(t) == "42"
}

pub fn term_to_string_unit_test() {
  let t = AstUnit(single("test.gleam", 1, 1))
  term_to_string(t) == "()"
}

pub fn term_to_string_type_test() {
  let t = Typ(single("test.gleam", 1, 1))
  term_to_string(t) == "Type"
}

// ============================================================================
// Value string representation
// ============================================================================

pub fn value_to_string_neut_variable_test() {
  let v = VNeut(HVar(0), [])
  value_to_string(v) == "v0"
}

pub fn value_to_string_neut_hole_test() {
  let v = VNeut(HHole(5), [])
  value_to_string(v) == "?5"
}

pub fn value_to_string_lambda_test() {
  let body = Var(0, single("test.gleam", 1, 1))
  let v = VLam(#("x", body), body)
  value_to_string(v) == "λx.?(-1)"
}

pub fn value_to_string_integer_literal_test() {
  let v = VLit(LitInt(42))
  value_to_string(v) == "42"
}

pub fn value_to_string_unit_test() {
  let v = VUnit
  value_to_string(v) == "()"
}

pub fn value_to_string_error_test() {
  let v = VErr
  value_to_string(v) == "<error>"
}
