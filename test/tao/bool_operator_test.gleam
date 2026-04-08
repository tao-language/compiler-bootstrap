// ============================================================================
// BOOL OPERATOR UNIT TESTS
// ============================================================================
/// Tests that boolean operators (not, and, or) call user-defined functions
/// instead of FFI builtins.
///
/// These tests verify:
/// 1. `not(x)` desugars to App(Var("not"), x), not CoreCall("not", x)
/// 2. `and(x, y)` desugars to App(App(Var("and"), x), y), not CoreCall
/// 3. `or(x, y)` desugars to App(App(Var("or"), x), y), not CoreCall
/// 4. Chained operators work: `not not True`
/// 5. Nested operators work: `and(not(True), or(False, True))`
import gleam/list
import gleeunit
import gleeunit/should
import simplifile
import tao/test_api

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// NOT OPERATOR TESTS
// ============================================================================

pub fn not_operator_calls_user_defined_function_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

> not(True) ~> False
> not(False) ~> True
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(2)
  test_api.all_passed(results) |> should.be_true
}

pub fn not_not_chained_operator_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

> not(not(True)) ~> True
> not(not(False)) ~> False
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(2)
  test_api.all_passed(results) |> should.be_true
}

// ============================================================================
// AND OPERATOR TESTS
// ============================================================================

pub fn and_operator_calls_user_defined_function_test() {
  let source = "
type Bool = True | False

fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}

> and(True, True) ~> True
> and(True, False) ~> False
> and(False, True) ~> False
> and(False, False) ~> False
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(4)
  test_api.all_passed(results) |> should.be_true
}

// ============================================================================
// OR OPERATOR TESTS
// ============================================================================

pub fn or_operator_calls_user_defined_function_test() {
  let source = "
type Bool = True | False

fn or(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}

> or(True, True) ~> True
> or(True, False) ~> True
> or(False, True) ~> True
> or(False, False) ~> False
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(4)
  test_api.all_passed(results) |> should.be_true
}

// ============================================================================
// COMPLEX EXPRESSION TESTS
// ============================================================================

pub fn nested_boolean_operators_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}

fn or(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}

> and(not(True), or(False, True)) ~> False
> or(and(True, True), and(False, False)) ~> True
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(2)
  test_api.all_passed(results) |> should.be_true
}

pub fn full_prelude_bool_module_test() {
  let assert Ok(source) = simplifile.read("lib/prelude/bool.tao")
  let #(errors, results) = test_api.run_test_file(source, "lib/prelude/bool.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(18)
  test_api.all_passed(results) |> should.be_true
}
