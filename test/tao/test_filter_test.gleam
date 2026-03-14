// ============================================================================
// TAO TEST FILTER TESTS
// ============================================================================
import tao/test_filter.{matches_pattern, filter_tests, file_base_name, list_test_names, count_by_annotation, AnnotationCounts}
import tao/test_parser.{type Test, Test, Expression as ExpectedExpr, type Annotation, Skip, Timeout, Group, IO}
import tao/syntax.{Int as TaoInt, Var}
import syntax/grammar.{Span}
import gleam/list
import gleeunit/should

// ============================================================================
// TEST: Exact match
// ============================================================================
pub fn matches_exact_pattern() {
  matches_pattern("integer addition", "integer addition") |> should.be_true
  matches_pattern("integer addition", "float addition") |> should.be_false
}

// ============================================================================
// TEST: Prefix wildcard match
// ============================================================================
pub fn matches_prefix_wildcard() {
  matches_pattern("parse *", "parse integer") |> should.be_true
  matches_pattern("parse *", "parse expression") |> should.be_true
  matches_pattern("parse *", "parse") |> should.be_true
  matches_pattern("parse *", "eval") |> should.be_false
}

// ============================================================================
// TEST: Suffix wildcard match
// ============================================================================
pub fn matches_suffix_wildcard() {
  matches_pattern("* addition", "integer addition") |> should.be_true
  matches_pattern("* addition", "float addition") |> should.be_true
  matches_pattern("* addition", "addition") |> should.be_true
  matches_pattern("* addition", "subtraction") |> should.be_false
}

// ============================================================================
// TEST: Substring wildcard match
// ============================================================================
pub fn matches_substring_wildcard() {
  matches_pattern("*add*", "add") |> should.be_true
  matches_pattern("*add*", "addition") |> should.be_true
  matches_pattern("*add*", "padding") |> should.be_true
  matches_pattern("*add*", "sub") |> should.be_false
}

// ============================================================================
// TEST: Multiple wildcards
// ============================================================================
pub fn matches_multiple_wildcards() {
  matches_pattern("* integer *", "test integer case") |> should.be_true
  matches_pattern("* integer *", "integer") |> should.be_true
  matches_pattern("* integer *", "test integer") |> should.be_true
  matches_pattern("* integer *", "integer case") |> should.be_true
  matches_pattern("* integer *", "float") |> should.be_false
}

// ============================================================================
// TEST: Empty pattern matches all
// ============================================================================
pub fn matches_empty_pattern() {
  matches_pattern("", "anything") |> should.be_true
}

// ============================================================================
// TEST: File base name extraction
// ============================================================================
pub fn extracts_file_base_name() {
  file_base_name("src/parser.tao") |> should.equal("parser")
  file_base_name("tests/math_test.tao") |> should.equal("math_test")
  file_base_name("lib/prelude/result.tao") |> should.equal("result")
  file_base_name("simple.tao") |> should.equal("simple")
}

// ============================================================================
// TEST: Filter tests by pattern
// ============================================================================
pub fn filters_tests_by_pattern() {
  let tests = [
    create_test("integer addition", []),
    create_test("float addition", []),
    create_test("integer subtraction", []),
  ]

  let filtered = filter_tests(tests, ["* addition"], "test.tao")
  filtered |> list.length |> should.equal(2)
}

// ============================================================================
// TEST: Filter tests matches filename too
// ============================================================================
pub fn filters_tests_matches_filename() {
  let tests = [
    create_test("some test", []),
    create_test("another test", []),
  ]

  // Should match because filename is "parser.tao" -> "parser"
  let filtered = filter_tests(tests, ["parser"], "parser.tao")
  filtered |> list.length |> should.equal(2)  // All tests in matching file
}

// ============================================================================
// TEST: Empty patterns match all tests
// ============================================================================
pub fn empty_patterns_match_all() {
  let tests = [
    create_test("test 1", []),
    create_test("test 2", []),
    create_test("test 3", []),
  ]

  let filtered = filter_tests(tests, [], "test.tao")
  filtered |> list.length |> should.equal(3)
}

// ============================================================================
// TEST: List test names
// ============================================================================
pub fn lists_test_names() {
  let tests = [
    create_test("integer addition", []),
    create_test("float addition", []),
    create_test("integer subtraction", []),
  ]

  let names = list_test_names(tests)
  names |> list.length |> should.equal(3)
  list.contains(names, "integer addition") |> should.be_true
  list.contains(names, "float addition") |> should.be_true
}

// ============================================================================
// TEST: Count annotations - skip
// ============================================================================
pub fn counts_skip_annotations() {
  let tests = [
    create_test("test 1", [Skip("")]),
    create_test("test 2", []),
    create_test("test 3", [Skip("reason")]),
  ]

  let counts = count_by_annotation(tests)
  counts.skip |> should.equal(2)
  counts.total |> should.equal(3)
}

// ============================================================================
// TEST: Count annotations - timeout
// ============================================================================
pub fn counts_timeout_annotations() {
  let tests = [
    create_test("test 1", [Timeout(5000)]),
    create_test("test 2", [Timeout(10000)]),
    create_test("test 3", []),
  ]

  let counts = count_by_annotation(tests)
  counts.timeout |> should.equal(2)
}

// ============================================================================
// TEST: Count annotations - group
// ============================================================================
pub fn counts_group_annotations() {
  let tests = [
    create_test("test 1", [Group("parser")]),
    create_test("test 2", [Group("lexer")]),
    create_test("test 3", []),
  ]

  let counts = count_by_annotation(tests)
  counts.group |> should.equal(2)
}

// ============================================================================
// TEST: Count annotations - io
// ============================================================================
pub fn counts_io_annotations() {
  let tests = [
    create_test("test 1", [IO]),
    create_test("test 2", []),
    create_test("test 3", [IO]),
  ]

  let counts = count_by_annotation(tests)
  counts.io |> should.equal(2)
}

// ============================================================================
// TEST: Count annotations - mixed
// ============================================================================
pub fn counts_mixed_annotations() {
  let tests = [
    create_test("test 1", [Skip(""), Group("slow")]),
    create_test("test 2", [Timeout(5000)]),
    create_test("test 3", []),
  ]

  let counts = count_by_annotation(tests)
  counts.total |> should.equal(3)
  counts.skip |> should.equal(1)
  counts.timeout |> should.equal(1)
  counts.group |> should.equal(1)
}

// ============================================================================
// TEST: Wildcard case sensitivity
// ============================================================================
pub fn wildcard_case_sensitivity() {
  matches_pattern("Parse *", "parse test") |> should.be_false
  matches_pattern("parse *", "Parse test") |> should.be_false
  matches_pattern("PARSE *", "parse test") |> should.be_false
}

// ============================================================================
// TEST: Consecutive wildcards
// ============================================================================
pub fn consecutive_wildcards() {
  matches_pattern("**", "anything") |> should.be_true
  matches_pattern("test**", "test") |> should.be_true
  matches_pattern("**test", "test") |> should.be_true
  matches_pattern("test**case", "test case") |> should.be_true
}

// ============================================================================
// Helper: Create a test
// ============================================================================
fn create_test(name: String, annotations: List(Annotation)) -> Test {
  let span = Span("test.tao", 0, 0, 0, 0)
  Test(
    name: name,
    expression: Var("x", span),
    expected: ExpectedExpr(TaoInt(0, span)),
    span: span,
    annotations: annotations,
  )
}
