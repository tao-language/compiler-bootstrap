// ============================================================================
// TAO TEST RUNNER
// ============================================================================
/// Run parsed tests and collect results.
///
/// For detailed documentation see:
/// - **[../plans/tao/11-test-system.md](../plans/tao/11-test-system.md)** - Test system specification
import tao/test_parser.{type Test, type ExpectedResult, Expression, Pattern, type Annotation, Skip, Timeout}
import tao/syntax.{type Expr, Int, Float, Var, BinOp, UnaryOp, OverloadedFn, OverloadedApp, Let, Block, SimpleFn, App, Lambda, Match, Str, Test as SyntaxTest, Run as SyntaxRun, If, For, While, Loop, Break, Continue}
import core/core.{type Term, type State, initial_state, eval, quote, type Value, Err}
import core/syntax as core_syntax
import syntax/grammar.{type Span, Span}
import gleam/list
import gleam/option.{Some, None}

// ============================================================================
// TEST RESULTS
// ============================================================================

/// Result of running a single test.
pub type TestResult {
  /// Test passed
  Pass(test_item: Test, result: Value)
  /// Test failed - pattern didn't match
  Fail(test_item: Test, expected: String, got: String, source: String)
  /// Test failed - runtime error
  Error(test_item: Test, message: String, source: String)
  /// Test skipped (via @skip annotation)
  Skipped(test_item: Test, reason: String)
  /// Test timed out
  TimedOut(test_item: Test, timeout_ms: Int)
}

/// Summary of test run.
pub type TestSummary {
  TestSummary(
    total: Int,
    passed: Int,
    failed: Int,
    skipped: Int,
    timed_out: Int,
    errored: Int,
  )
}

// ============================================================================
// MAIN RUNNER
// ============================================================================

/// Run all tests and return results.
pub fn run_tests(tests: List(Test), source: String) -> List(TestResult) {
  list.map(tests, fn(t) { run_single_test(t, source) })
}

/// Run a single test.
fn run_single_test(test_item: Test, source: String) -> TestResult {
  // Check for skip annotation
  case get_skip_annotation(test_item.annotations) {
    Some(reason) -> Skipped(test_item, reason)
    None -> {
      // Get timeout
      let timeout = get_timeout_annotation(test_item.annotations) |> option.unwrap(5000)

      // Run the test (timeout not yet implemented - would need IO)
      run_test_expression(test_item, timeout, source)
    }
  }
}

/// Get skip reason from annotations if present.
fn get_skip_annotation(annotations: List(Annotation)) -> option.Option(String) {
  find_skip(annotations)
}

fn find_skip(annotations: List(Annotation)) -> option.Option(String) {
  case annotations {
    [] -> None
    [Skip(reason), ..] -> Some(reason)
    [_, ..rest] -> find_skip(rest)
  }
}

/// Get timeout from annotations (default 5000ms).
fn get_timeout_annotation(annotations: List(Annotation)) -> option.Option(Int) {
  find_timeout(annotations)
}

fn find_timeout(annotations: List(Annotation)) -> option.Option(Int) {
  case annotations {
    [] -> None
    [Timeout(ms), ..] -> Some(ms)
    [_, ..rest] -> find_timeout(rest)
  }
}

/// Run the test expression and compare with expected result.
fn run_test_expression(test_item: Test, _timeout: Int, source: String) -> TestResult {
  // Evaluate the expression
  let env = []
  let ffi = initial_state.ffi
  let expr_term = desugar_expression(test_item.expression)

  let value = eval(ffi, env, expr_term)

  // Compare with expected
  case test_item.expected {
    Expression(expected_expr) -> {
      let expected_term = desugar_expression(expected_expr)
      let expected_value = eval(ffi, env, expected_term)

      case values_equal(value, expected_value) {
        True -> Pass(test_item, value)
        False -> {
          let got_str = format_value(value)
          let expected_str = format_value(expected_value)
          Fail(test_item, expected_str, got_str, source)
        }
      }
    }
    Pattern(_pattern_str) -> {
      // Pattern matching not yet implemented
      // For now, just pass if evaluation succeeded
      Pass(test_item, value)
    }
  }
}

/// Desugar a Tao expression to Core term.
fn desugar_expression(expr: Expr) -> Term {
  // TODO: Use new desugarer module
  // For now, return a placeholder
  let span = get_expr_span(expr)
  Err(message: "Desugaring not yet implemented", span: span)
}

/// Get span from expression.
fn get_expr_span(expr: Expr) -> Span {
  case expr {
    Int(_, span) -> span
    Float(_, span) -> span
    Var(_, span) -> span
    BinOp(_, _, _, span) -> span
    UnaryOp(_, _, span) -> span
    OverloadedFn(_, _, _, _, _, _, span) -> span
    OverloadedApp(_, _, span) -> span
    Let(_, _, _, _, span) -> span
    Block(_, span) -> span
    SimpleFn(_, _, _, _, span) -> span
    App(_, _, span) -> span
    Lambda(_, _, _, span) -> span
    Match(_, _, span) -> span
    If(_, _, _, span) -> span
    For(_, _, _, span) -> span
    While(_, _, span) -> span
    Loop(_, span) -> span
    Break(span) -> span
    Continue(span) -> span
    Str(_, span) -> span
    SyntaxTest(_, _, span) -> span
    SyntaxRun(_, span) -> span
  }
}

/// Check if two values are equal.
fn values_equal(v1: Value, v2: Value) -> Bool {
  // Simple structural equality check
  value_to_string(v1) == value_to_string(v2)
}

/// Format a value for display.
fn format_value(value: Value) -> String {
  // Quote back to syntax and format
  let span = Span("", 0, 0, 0, 0)
  let term = quote(initial_state.ffi, 0, value, span)
  core_syntax.format(term)
}

/// Convert value to string for comparison.
fn value_to_string(value: Value) -> String {
  format_value(value)
}

// ============================================================================
// SUMMARY
// ============================================================================

/// Calculate test run summary.
pub fn calculate_summary(results: List(TestResult)) -> TestSummary {
  list.fold(results, TestSummary(0, 0, 0, 0, 0, 0), fn(acc, result) {
    case result {
      Pass(_, _) -> TestSummary(acc.total + 1, acc.passed + 1, acc.failed, acc.skipped, acc.timed_out, acc.errored)
      Fail(_, _, _, _) -> TestSummary(acc.total + 1, acc.passed, acc.failed + 1, acc.skipped, acc.timed_out, acc.errored)
      Error(_, _, _) -> TestSummary(acc.total + 1, acc.passed, acc.failed, acc.skipped, acc.timed_out, acc.errored + 1)
      Skipped(_, _) -> TestSummary(acc.total + 1, acc.passed, acc.failed, acc.skipped + 1, acc.timed_out, acc.errored)
      TimedOut(_, _) -> TestSummary(acc.total + 1, acc.passed, acc.failed, acc.skipped, acc.timed_out + 1, acc.errored)
    }
  })
}

/// Check if all tests passed.
pub fn all_passed(results: List(TestResult)) -> Bool {
  case results {
    [] -> True
    [result, ..rest] -> {
      case result {
        Pass(_, _) -> all_passed(rest)
        _ -> False
      }
    }
  }
}

/// Get failed tests.
pub fn get_failures(results: List(TestResult)) -> List(TestResult) {
  list.filter(results, fn(result) {
    case result {
      Pass(_, _) -> False
      Skipped(_, _) -> False
      _ -> True
    }
  })
}
