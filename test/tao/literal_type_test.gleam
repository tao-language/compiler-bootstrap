// Integration tests for polymorphic numeric literals in Tao source.
// These test the full pipeline: parse → desugar → type check → evaluate.
import gleeunit
import gleeunit/should
import gleam/list
import tao/test_api

pub fn main() {
  gleeunit.main()
}

/// Test: integer literal checked against I32 annotation
pub fn int_literal_as_i32_test() {
  let source = "
let x: I32 = 42
> x ~> 42
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  test_api.all_passed(results) |> should.be_true
}

/// Test: integer literal checked against I64 annotation
pub fn int_literal_as_i64_test() {
  let source = "
let x: I64 = 42
> x ~> 42
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  test_api.all_passed(results) |> should.be_true
}

/// Test: integer literal checked against F64 annotation (int→float coercion)
pub fn int_literal_as_f64_test() {
  let source = "
let x: F64 = 42
> x ~> _
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  test_api.all_passed(results) |> should.be_true
}

/// Test: integer literal checked against F32 annotation
pub fn int_literal_as_f32_test() {
  let source = "
let x: F32 = 42
> x ~> _
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  test_api.all_passed(results) |> should.be_true
}

/// Test: float literal checked against F64 annotation
pub fn float_literal_as_f64_test() {
  let source = "
let x: F64 = 3.14
> x ~> 3.14
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  test_api.all_passed(results) |> should.be_true
}

/// Test: float literal checked against F32 annotation
pub fn float_literal_as_f32_test() {
  let source = "
let x: F32 = 3.14
> x ~> 3.14
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  test_api.all_passed(results) |> should.be_true
}

/// Test: float literal checked against I32 should FAIL
pub fn float_literal_as_i32_fails_test() {
  let source = "
let x: I32 = 3.14
> x ~> _
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  // Should have type errors
  list.is_empty(errors) |> should.be_false
}

/// Test: float literal checked against I64 should FAIL
pub fn float_literal_as_i64_fails_test() {
  let source = "
let x: I64 = 3.14
> x ~> _
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  list.is_empty(errors) |> should.be_false
}

/// Test: unannotated integer literal (inferred)
pub fn unannotated_int_literal_test() {
  let source = "
let x = 42
> x ~> 42
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  test_api.all_passed(results) |> should.be_true
}

/// Test: unannotated float literal (inferred)
pub fn unannotated_float_literal_test() {
  let source = "
let x = 3.14
> x ~> 3.14
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  test_api.all_passed(results) |> should.be_true
}

/// Test: arithmetic on integer literals
pub fn int_literal_arithmetic_test() {
  let source = "
> 40 + 2 ~> 42
> 50 - 8 ~> 42
> 6 * 7 ~> 42
> 84 / 2 ~> 42
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(4)
  test_api.all_passed(results) |> should.be_true
}

/// Test: arithmetic on float literals
pub fn float_literal_arithmetic_test() {
  let source = "
> 1.5 + 2.5 ~> 4.0
> 10.0 - 3.0 ~> 7.0
> 2.0 * 3.0 ~> 6.0
> 10.0 / 2.0 ~> 5.0
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(4)
  test_api.all_passed(results) |> should.be_true
}

/// Test: mixed integer/float in same file
pub fn mixed_types_test() {
  let source = "
let a: I32 = 42
let b: F64 = 3.14
let c: U32 = 100
let d: I64 = 999

> a ~> 42
> c ~> 100
> d ~> 999
"
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  test_api.all_passed(results) |> should.be_true
}
