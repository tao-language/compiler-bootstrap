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
  list.length(results) |> should.equal(14)
  test_api.all_passed(results) |> should.be_true
}

// ============================================================================
// INFIX OPERATOR TESTS
// ============================================================================

pub fn and_operator_infix_syntax_test() {
  let source = "
type Bool = True | False

fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}

> False and True ~> False
> True and True ~> True
> True and False ~> False
> False and False ~> False
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(4)
  test_api.all_passed(results) |> should.be_true
}

pub fn or_operator_infix_syntax_test() {
  let source = "
type Bool = True | False

fn or(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}

> False or True ~> True
> True or True ~> True
> True or False ~> True
> False or False ~> False
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(4)
  test_api.all_passed(results) |> should.be_true
}

pub fn mixed_infix_and_function_call_test() {
  let source = "
type Bool = True | False

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

> and(False, True) ~> False
> False and True ~> False
> or(True, False) ~> True
> True or False ~> True
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(4)
  test_api.all_passed(results) |> should.be_true
}

pub fn symbol_infix_operators_test() {
  let source = "
type Bool = True | False

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

> False && True ~> False
> True && True ~> True
> False || True ~> True
> True || False ~> True
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(4)
  test_api.all_passed(results) |> should.be_true
}

// ============================================================================
// IMPORT RESOLUTION TESTS
// ============================================================================

/// Test that imported prelude functions with Python-style operators work correctly.
/// This was the root cause bug: function bodies were desugared without
/// constructor environment, causing True/False to become holes.
pub fn imported_python_style_operators_test() {
  let source = "
import prelude/bool {Bool, and, or, not}

> True and True ~> True
> False and True ~> False
> True or False ~> True
> not False ~> True
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(4)
  test_api.all_passed(results) |> should.be_true
}

/// Test nested Python-style operators with imports
pub fn imported_nested_python_style_operators_test() {
  let source = "
import prelude/bool {Bool, and, or, not}

> True and True and True
True

> False or False or False
False

> (True or False) and not False
True

> (True and False) or not False
True

> not not True
True

> not not not False
True
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(6)
  test_api.all_passed(results) |> should.be_true
}

/// Test mixed function call and Python-style syntax with imports
pub fn imported_mixed_syntax_styles_test() {
  let source = "
import prelude/bool {Bool, and, or, not}

> and(True, True) ~> True
> False and True ~> False
> or(False, True) ~> True
> not False ~> True
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(4)
  test_api.all_passed(results) |> should.be_true
}

/// Test that prelude bool module with Python-style operators passes
pub fn prelude_bool_module_python_style_test() {
  let source = "// Prelude Bool module
// Boolean type and logical operations

/// Boolean type with two constructors
type Bool = True | False

/// Negate a boolean value
fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

> not True ~> False
> not False ~> True

/// Logical AND with short-circuit evaluation
fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}

> True and True ~> True
> True and False ~> False
> False and True ~> False
> False and False ~> False

/// Logical OR with short-circuit evaluation
fn or(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}

> True or True ~> True
> True or False ~> True
> False or True ~> True
> False or False ~> False
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(10)
  test_api.all_passed(results) |> should.be_true
}

/// Test that the full prelude bool.tao file passes all tests
pub fn full_prelude_bool_tao_test() {
  let assert Ok(source) = simplifile.read("lib/prelude/bool.tao")
  let #(errors, results) = test_api.run_test_file(source, "lib/prelude/bool.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(14)
  test_api.all_passed(results) |> should.be_true
}

/// Test that the prelude bool.test.tao file passes with Python-style operators
pub fn prelude_bool_test_tao_test() {
  let assert Ok(source) = simplifile.read("lib/prelude/bool.test.tao")
  let #(errors, results) = test_api.run_test_file(source, "lib/prelude/bool.test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(6)
  test_api.all_passed(results) |> should.be_true
}
