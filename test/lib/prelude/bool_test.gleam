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
import gleam/list
import gleam/string
import gleeunit
import gleeunit/should
import simplifile
import tao/test_api

pub fn main() {
  gleeunit.main()
}

pub fn lib_prelude_bool_module_test() {
  let filename = "lib/prelude/bool.tao"
  let assert Ok(source) = simplifile.read(filename)
  let #(errors, results) = test_api.run_test_file(source, filename)
  errors |> should.equal([])
  list.length(results) |> should.equal(18)
}

pub fn lib_prelude_bool_test_test() {
  let filename = "lib/prelude/bool.test.tao"
  let assert Ok(source) = simplifile.read(filename)
  let #(errors, results) = test_api.run_test_file(source, filename)
  errors |> should.equal([])
  list.length(results) |> should.equal(6)
}
