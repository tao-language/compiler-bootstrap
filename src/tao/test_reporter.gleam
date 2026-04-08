// ============================================================================
// TAO TEST REPORTER
// ============================================================================
/// Test reporting for the test_api module.
///
/// Reports test results with summary information. Works with the simpler
/// test_api.TestResult type: Pass(expression) | Fail(expression, expected, actual).
import tao/test_api.{type TestResult, type TestSummary, TestSummary, Pass, Fail}
import gleam/int
import gleam/io
import gleam/list

// ============================================================================
// MAIN REPORTING
// ============================================================================

/// Report all test results with summary.
pub fn report_results(
  results: List(TestResult),
  summary: TestSummary,
  verbose: Bool,
) -> Nil {
  // Report individual results
  case verbose {
    True -> list.each(results, report_result_verbose)
    False -> list.each(results, report_result_condensed)
  }

  // Report summary
  report_summary(summary)
}

/// Report a single test result in verbose mode (shows all tests).
fn report_result_verbose(result: TestResult) -> Nil {
  case result {
    Pass(expression) -> {
      io.println("✓ " <> expression)
    }
    Fail(expression, expected, actual) -> {
      io.println("✗ FAIL: " <> expression)
      io.println("    expected: " <> expected)
      io.println("    actual:   " <> actual)
      io.println("")
    }
  }
}

/// Report a single test result in condensed mode (only failures).
fn report_result_condensed(result: TestResult) -> Nil {
  case result {
    Pass(_) -> Nil  // Skip passed tests in condensed mode
    Fail(expression, expected, actual) -> {
      io.println("✗ FAIL: " <> expression)
      io.println("    expected: " <> expected)
      io.println("    actual:   " <> actual)
      io.println("")
    }
  }
}

/// Report test summary.
fn report_summary(summary: TestSummary) -> Nil {
  io.println("────────────────────────────────────────")
  io.println("Test Summary:")
  io.println("  Total:  " <> int.to_string(summary.total))
  io.println("  Passed: " <> int.to_string(summary.passed))
  io.println("  Failed: " <> int.to_string(summary.failed))
  io.println("")
}

/// List test expressions from results (for --list mode, shows all test expressions).
pub fn list_test_expressions(results: List(TestResult)) -> Nil {
  io.println("Available tests:")
  io.println("")
  list.each(results, fn(r) {
    case r {
      Pass(expr) -> io.println("  - " <> expr)
      Fail(expr, _, _) -> io.println("  - " <> expr)
    }
  })
  io.println("")
  io.println("Total: " <> int.to_string(list.length(results)) <> " tests")
}

/// Report final status message.
pub fn report_final_status(all_passed: Bool) -> Nil {
  case all_passed {
    True -> io.println("✓ All tests passed!")
    False -> io.println("✗ Some tests failed")
  }
}
