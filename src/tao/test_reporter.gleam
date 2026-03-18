// ============================================================================
// TAO TEST REPORTER
// ============================================================================
/// Enhanced test reporting with summary, colors, and source snippets.
///
/// For detailed documentation see:
/// - **[../plans/tao/enhanced-test-framework-plan.md](../plans/tao/enhanced-test-framework-plan.md)** - Implementation plan
import tao/test_parser.{type Test, Test}
import tao/test_runner.{type TestResult, type TestSummary, TestSummary, Pass, Fail, Error, Skipped, TimedOut}
import syntax/grammar.{type Span}
import gleam/list
import gleam/int
import gleam/io
import gleam/string

// ============================================================================
// MAIN REPORTING
// ============================================================================

/// Report all test results with summary.
pub fn report_results(
  results: List(TestResult),
  summary: TestSummary,
  verbose: Bool,
  _source: String,
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
    Pass(t, _result) -> {
      case t {
        Test(name, _, _, _, _) -> {
          io.println("✓ Test: " <> name)
        }
      }
    }
    Fail(t, expected, got) -> {
      case t {
        Test(name, _, _, _, _) -> {
          io.println("✗ FAIL: " <> name)
          io.println("    Expected: " <> expected)
          io.println("    Got:      " <> got)
          io.println("")
        }
      }
    }
    Error(t, message) -> {
      case t {
        Test(name, _, _, _, _) -> {
          io.println("⚠ ERROR: " <> name)
          io.println("    Message: " <> message)
          io.println("")
        }
      }
    }
    Skipped(t, reason) -> {
      case t {
        Test(name, _, _, _, _) -> {
          io.println("○ SKIP: " <> name)
          io.println("    Reason: " <> reason)
          io.println("")
        }
      }
    }
    TimedOut(t, timeout_ms) -> {
      case t {
        Test(name, _, _, _, _) -> {
          io.println("⚠ TIMEOUT: " <> name)
          io.println("    Timeout: " <> int.to_string(timeout_ms) <> "ms")
          io.println("")
        }
      }
    }
  }
}

/// Report a single test result in condensed mode (only failures).
fn report_result_condensed(result: TestResult) -> Nil {
  case result {
    Pass(_, _) -> Nil  // Skip passed tests in condensed mode
    Fail(t, expected, got) -> {
      case t {
        Test(name, _, _, _, _) -> {
          io.println("✗ FAIL: " <> name)
          io.println("    Expected: " <> expected)
          io.println("    Got:      " <> got)
          io.println("")
        }
      }
    }
    Error(t, message) -> {
      case t {
        Test(name, _, _, _, _) -> {
          io.println("⚠ ERROR: " <> name)
          io.println("    Message: " <> message)
          io.println("")
        }
      }
    }
    Skipped(t, reason) -> {
      case t {
        Test(name, _, _, _, _) -> {
          io.println("○ SKIP: " <> name <> " (" <> reason <> ")")
        }
      }
    }
    TimedOut(t, timeout_ms) -> {
      case t {
        Test(name, _, _, _, _) -> {
          io.println("⚠ TIMEOUT: " <> name <> " (" <> int.to_string(timeout_ms) <> "ms)")
        }
      }
    }
  }
}

/// Report test summary.
fn report_summary(summary: TestSummary) -> Nil {
  io.println("────────────────────────────────────────")
  io.println("Test Summary:")
  io.println("  Total:     " <> int.to_string(summary.total))
  io.println("  Passed:    " <> int.to_string(summary.passed))
  io.println("  Failed:    " <> int.to_string(summary.failed))
  io.println("  Skipped:   " <> int.to_string(summary.skipped))
  io.println("  Errors:    " <> int.to_string(summary.errored))
  io.println("  Timed Out: " <> int.to_string(summary.timed_out))
  io.println("")
}

/// List test names (for --list mode).
pub fn list_test_names(tests: List(Test)) -> Nil {
  io.println("Available tests:")
  io.println("")
  list.each(tests, fn(t) {
    io.println("  - " <> t.name)
  })
  io.println("")
  io.println("Total: " <> int.to_string(list.length(tests)) <> " tests")
}

/// Report final status message.
pub fn report_final_status(all_passed: Bool) -> Nil {
  case all_passed {
    True -> io.println("✓ All tests passed!")
    False -> io.println("✗ Some tests failed")
  }
}
