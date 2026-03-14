// ============================================================================
// TAO TEST PARSER TESTS
// ============================================================================
import tao/test_parser.{parse_tests, ParseTestsResult, Test, Expression, Pattern, Skip, Timeout, Group, IO, Retry, Requires}
import gleam/string
import gleam/list
import gleeunit/should

// ============================================================================
// TEST: Parse single-line test
// ============================================================================
pub fn parse_single_line_test() {
  let source = "> 1 + 2 ~> 3"
  let result = parse_tests(source, "test.tao")

  result.tests |> list.length |> should.equal(1)

  let assert [test_item] = result.tests
  test_item.name |> should.equal("1 + 2")
  result.syntax_errors |> list.length |> should.equal(0)
}

// ============================================================================
// TEST: Parse multi-line test with name
// ============================================================================
pub fn parse_multi_line_test_with_name() {
  let source = ["-- integer addition", "> 1 + 2", "3"] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  result.tests |> list.length |> should.equal(1)

  let assert [test_item] = result.tests
  test_item.name |> should.equal("integer addition")
  result.syntax_errors |> list.length |> should.equal(0)
}

// ============================================================================
// TEST: Parse multiple tests
// ============================================================================
pub fn parse_multiple_tests() {
  let source = [
    "-- integer addition",
    "> 1 + 2",
    "3",
    "",
    "-- integer subtraction",
    "> 5 - 3",
    "2",
  ] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  result.tests |> list.length |> should.equal(2)
  result.syntax_errors |> list.length |> should.equal(0)
}

// ============================================================================
// TEST: Parse test with @skip annotation
// ============================================================================
pub fn parse_test_with_skip_annotation() {
  let source = ["-- @skip", "-- flaky test", "> flaky_operation()", "result"] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  result.tests |> list.length |> should.equal(1)

  let assert [test_item] = result.tests
  test_item.annotations |> list.length |> should.equal(1)

  let assert [Skip(reason)] = test_item.annotations
  reason |> should.equal("")
}

// ============================================================================
// TEST: Parse test with @skip reason
// ============================================================================
pub fn parse_test_with_skip_reason() {
  let source = [
    "-- @skip not implemented yet",
    "-- future feature",
    "> future_feature()",
    "result",
  ] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  let assert [test_item] = result.tests
  let assert [Skip(reason)] = test_item.annotations
  reason |> should.equal("not implemented yet")
}

// ============================================================================
// TEST: Parse test with @timeout annotation
// ============================================================================
pub fn parse_test_with_timeout_annotation() {
  let source = ["-- @timeout 5000", "-- slow test", "> slow_operation()", "result"] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  let assert [test_item] = result.tests
  let assert [Timeout(ms)] = test_item.annotations
  ms |> should.equal(5000)
}

// ============================================================================
// TEST: Parse test with @group annotation
// ============================================================================
pub fn parse_test_with_group_annotation() {
  let source = ["-- @group parser", "-- parser test", "> parse_expression()", "result"] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  let assert [test_item] = result.tests
  let assert [Group(name)] = test_item.annotations
  name |> should.equal("parser")
}

// ============================================================================
// TEST: Parse test with @io annotation
// ============================================================================
pub fn parse_test_with_io_annotation() {
  let source = ["-- @io", "-- file operation", "> read_file()", "result"] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  let assert [test_item] = result.tests
  let assert [IO] = test_item.annotations
}

// ============================================================================
// TEST: Parse test with @retry annotation
// ============================================================================
pub fn parse_test_with_retry_annotation() {
  let source = ["-- @retry 3", "-- flaky network test", "> network_call()", "result"] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  let assert [test_item] = result.tests
  let assert [Retry(count)] = test_item.annotations
  count |> should.equal(3)
}

// ============================================================================
// TEST: Parse test with @requires annotation
// ============================================================================
pub fn parse_test_with_requires_annotation() {
  let source = [
    "-- @requires setup_test",
    "-- dependent test",
    "> dependent_operation()",
    "result",
  ] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  let assert [test_item] = result.tests
  let assert [Requires(name)] = test_item.annotations
  name |> should.equal("setup_test")
}

// ============================================================================
// TEST: Parse test with multiple annotations
// ============================================================================
pub fn parse_test_with_multiple_annotations() {
  let source = [
    "-- @skip",
    "-- @group slow",
    "-- @timeout 10000",
    "-- slow skipped test",
    "> slow_operation()",
    "result",
  ] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  let assert [test_item] = result.tests
  test_item.annotations |> list.length |> should.equal(3)
}

// ============================================================================
// TEST: Parse multi-line expression
// ============================================================================
pub fn parse_multi_line_expression() {
  let source = [
    "-- let binding test",
    "> let x = 1",
    "> let y = 2",
    "> x + y",
    "3",
  ] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  result.tests |> list.length |> should.equal(1)
  result.syntax_errors |> list.length |> should.equal(0)
}

// ============================================================================
// TEST: Parse test with pattern expected result
// ============================================================================
pub fn parse_test_with_pattern_expected() {
  let source = ["-- pattern match test", "> Some(42)", "Some(_)"] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  let assert [test_item] = result.tests
  // Pattern results are stored as strings for now
  case test_item.expected {
    Pattern(pattern) -> pattern |> should.equal("Some(_)")
    Expression(_) -> panic as "Expected Pattern, got Expression"
  }
}

// ============================================================================
// TEST: Empty source returns no tests
// ============================================================================
pub fn parse_empty_source() {
  let source = ""
  let result = parse_tests(source, "test.tao")

  result.tests |> list.length |> should.equal(0)
  result.syntax_errors |> list.length |> should.equal(0)
}

// ============================================================================
// TEST: Source with only comments returns no tests
// ============================================================================
pub fn parse_only_comments() {
  let source = ["-- This is a comment", "-- Another comment"] |> string.join("\n")

  let result = parse_tests(source, "test.tao")

  result.tests |> list.length |> should.equal(0)
  result.syntax_errors |> list.length |> should.equal(0)
}

// ============================================================================
// TEST: Test without expected result is syntax error
// ============================================================================
pub fn parse_test_without_expected_result() {
  let source = "-- missing expected\n> 1 + 2"

  let result = parse_tests(source, "test.tao")

  result.syntax_errors |> list.length |> should.equal(1)
}
