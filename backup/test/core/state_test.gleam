// ============================================================================
// STATE TESTS
// ============================================================================
/// Tests for the state module — type checking state management and error handling.

import core/ast as ast
import gleam/list
import core/state.{type Error, TypeMismatch, VarUndefined, HoleUnsolved, initial_state, with_err, State, with_truth_ctor, new_hole, new_hole_value, new_hole_unify, new_var, def_var, lookup_var}
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

const span = Span("state_test", 1, 1, 1, 1)

fn vint() { ast.VLitT(ast.I32T) }
fn vbool() { ast.VLitT(ast.I64T) }
fn vstr() { ast.VLitT(ast.F64T) }

// ============================================================================
// INITIAL STATE
// ============================================================================

pub fn initial_state_default_test() {
  let s = initial_state
  s.hole_counter |> should.equal(0)
  s.var_counter |> should.equal(0)
  s.level |> should.equal(0)
  s.lambda_depth |> should.equal(0)
  s.hole_depths |> should.equal([])
  s.step_counter |> should.equal(0)
  s.max_steps |> should.equal(10000)
  s.ffi |> should.equal([])
  s.ctrs |> should.equal([])
  s.vars |> should.equal([])
  s.subst |> should.equal([])
  s.errors |> should.equal([])
  s.warnings |> should.equal([])
  s.truth_ctor |> should.equal("True")
}

pub fn with_truth_ctor_test() {
  let s = initial_state
  let s2 = with_truth_ctor(s, "No")
  s.truth_ctor |> should.equal("True")
  s2.truth_ctor |> should.equal("No")
  s2.hole_counter |> should.equal(s.hole_counter)
}

// ============================================================================
// ERROR HANDLING
// ============================================================================

pub fn with_err_adds_error_test() {
  let err = TypeMismatch(expected: vint(), got: vbool(), expected_span: span, got_span: span)
  let s = State(..initial_state, errors: [])
  let s2 = with_err(s, err)
  list.length(s2.errors) |> should.equal(1)
  s.errors |> should.equal([])
}

pub fn with_err_accumulates_test() {
  let err1 = TypeMismatch(expected: vint(), got: vbool(), expected_span: span, got_span: span)
  let err2 = VarUndefined(index: 1, span: span)
  let s = State(..initial_state, errors: [])
  let s2 = with_err(s, err1)
  let s3 = with_err(s2, err2)
  list.length(s3.errors) |> should.equal(2)
}

pub fn error_type_mismatch_construction_test() {
  let err = TypeMismatch(expected: vint(), got: vbool(), expected_span: span, got_span: span)
  case err {
    TypeMismatch(..) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn error_var_undefined_construction_test() {
  let err = VarUndefined(index: 42, span: span)
  case err {
    VarUndefined(index: idx, span: _) -> {
      idx |> should.equal(42)
      span |> should.equal(span)
    }
    _ -> False |> should.be_true
  }
}

pub fn error_hole_unsolved_construction_test() {
  let err = HoleUnsolved(id: 99, span: span)
  case err {
    HoleUnsolved(id: id, span: _) -> {
      id |> should.equal(99)
      span |> should.equal(span)
    }
    _ -> False |> should.be_true
  }
}

// ============================================================================
// HOLE CREATION
// ============================================================================

pub fn new_hole_test() {
  let s = initial_state
  let #(id, s2) = new_hole(s)
  id |> should.equal(0)
  s2.hole_counter |> should.equal(1)

  let #(id2, s3) = new_hole(s2)
  id2 |> should.equal(1)
  s3.hole_counter |> should.equal(2)
}

pub fn new_hole_value_test() {
  let s = initial_state
  let #(hole, s2) = new_hole_value(s, 0)

  case hole {
    ast.VNeut(ast.HHole(0), []) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  s2.hole_depths |> should.equal([#(0, 0)])
  s2.hole_counter |> should.equal(1)
}

pub fn new_hole_value_multiple_test() {
  let s = initial_state
  let #(hole1, s2) = new_hole_value(s, 0)
  let #(hole2, s3) = new_hole_value(s2, 1)
  let #(hole3, s4) = new_hole_value(s3, 1)

  case hole1 {
    ast.VNeut(ast.HHole(0), _) -> True
    _ -> False
  } |> should.be_true
  case hole2 {
    ast.VNeut(ast.HHole(1), _) -> True
    _ -> False
  } |> should.be_true
  case hole3 {
    ast.VNeut(ast.HHole(2), _) -> True
    _ -> False
  } |> should.be_true

  s4.hole_depths |> should.equal([#(2, 1), #(1, 1), #(0, 0)])
}

pub fn new_hole_unify_test() {
  let s = initial_state
  let #(hole, s2) = new_hole_unify(s)

  case hole {
    ast.VNeut(ast.HHole(0), []) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  s2.hole_depths |> should.equal([])
  s2.hole_counter |> should.equal(1)
}

// ============================================================================
// VARIABLE MANAGEMENT
// ============================================================================

pub fn new_var_test() {
  let s = initial_state
  let #(id, s2) = new_var(s)
  id |> should.equal(0)
  s2.var_counter |> should.equal(1)
}

pub fn def_var_test() {
  let s = initial_state
  let s2 = def_var(s, "x", vint(), vint())

  case lookup_var(s2, "x") {
    Ok(#(val, typ)) -> {
      case val {
        ast.VLitT(ast.I32T) -> True |> should.be_true
        _ -> False |> should.be_true
      }
      case typ {
        ast.VLitT(ast.I32T) -> True |> should.be_true
        _ -> False |> should.be_true
      }
    }
    Error(..) -> False |> should.be_true
  }
}

pub fn def_var_multiple_test() {
  let s = initial_state
  let s1 = def_var(s, "a", vint(), vint())
  let s2 = def_var(s1, "b", vbool(), vbool())

  case lookup_var(s2, "b") {
    Ok(#(val, _)) -> case val {
      ast.VLitT(ast.I64T) -> True
      _ -> False
    } |> should.be_true
    Error(..) -> False |> should.be_true
  }
  case lookup_var(s2, "a") {
    Ok(#(val, _)) -> case val {
      ast.VLitT(ast.I32T) -> True
      _ -> False
    } |> should.be_true
    Error(..) -> False |> should.be_true
  }
}

pub fn lookup_var_not_found_test() {
  let s = initial_state
  case lookup_var(s, "nonexistent") {
    Ok(_) -> False |> should.be_true
    Error(..) -> True |> should.be_true
  }
}

// ============================================================================
// STATE MODIFICATION
// ============================================================================

pub fn state_immutability_test() {
  let s = initial_state
  let err1 = TypeMismatch(expected: vint(), got: vbool(), expected_span: span, got_span: span)
  let err2 = VarUndefined(index: 1, span: span)
  let s2 = with_err(s, err1)
  let s3 = with_err(s, err2)
  s.errors |> should.equal([])
  s2.errors |> should.equal([err1])
  s3.errors |> should.equal([err2])
}

pub fn state_preserves_all_fields_test() {
  let s = State(
    ..initial_state,
    errors: [VarUndefined(index: 0, span: span)],
    hole_counter: 5,
    level: 3,
    truth_ctor: "Custom",
  )
  let err = TypeMismatch(expected: vint(), got: vbool(), expected_span: span, got_span: span)
  let s2 = with_err(s, err)
  s2.errors |> should.equal([err, VarUndefined(index: 0, span: span)])
  s2.hole_counter |> should.equal(5)
  s2.level |> should.equal(3)
  s2.truth_ctor |> should.equal("Custom")
}
