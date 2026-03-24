// ============================================================================
// STDLIB PRELUDE TESTS
// ============================================================================
/// Tests for standard library prelude modules.
///
/// These tests verify that:
/// 1. No syntax/type/exhaustiveness errors in the module
/// 2. At least one test ran (results != [])
///
/// For detailed documentation see:
/// - **[../plans/prelude/README.md](../plans/prelude/README.md)** - Prelude implementation plan
/// - **[../plans/tao/18-stdlib-testing.md](../plans/tao/18-stdlib-testing.md)** - Testing infrastructure
import tao/test_api
import gleam/string
import gleam/list
import simplifile
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// BOOL MODULE TESTS
// ============================================================================

pub fn prelude_bool_module_no_errors_test() {
  let assert Ok(source) = simplifile.read("lib/prelude/bool.tao")
  let #(errors, _results) = test_api.run_test_file(source, "lib/prelude/bool.tao")
  errors |> should.equal([])
}

pub fn prelude_bool_module_tests_run_test() {
  let assert Ok(source) = simplifile.read("lib/prelude/bool.tao")
  let #(_errors, results) = test_api.run_test_file(source, "lib/prelude/bool.tao")
  list.is_empty(results) |> should.be_false
}

// ============================================================================
// BOOL TEST FILE TESTS
// ============================================================================

pub fn prelude_bool_test_file_no_errors_test() {
  let assert Ok(source) = simplifile.read("test/lib/prelude/bool_test.tao")
  let #(errors, _results) = test_api.run_test_file(source, "test/lib/prelude/bool_test.tao")
  errors |> should.equal([])
}

pub fn prelude_bool_test_file_tests_run_test() {
  let assert Ok(source) = simplifile.read("test/lib/prelude/bool_test.tao")
  let #(_errors, results) = test_api.run_test_file(source, "test/lib/prelude/bool_test.tao")
  list.is_empty(results) |> should.be_false
}

pub fn prelude_bool_test_file_all_pass_test() {
  let assert Ok(source) = simplifile.read("test/lib/prelude/bool_test.tao")
  let #(errors, results) = test_api.run_test_file(source, "test/lib/prelude/bool_test.tao")
  
  // No errors
  errors |> should.equal([])
  
  // All tests should pass
  let failures = list.filter(results, is_fail)
  failures |> should.equal([])
}

// ============================================================================
// HELPERS
// ============================================================================

fn is_fail(result: test_api.TestResult) -> Bool {
  case result {
    test_api.Pass(_) -> False
    test_api.Fail(_, _, _) -> True
  }
}
