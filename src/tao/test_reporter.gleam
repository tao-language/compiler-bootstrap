// ============================================================================
// TAO TEST REPORTER
// ============================================================================
/// Enhanced test reporting with summary, colors, and source snippets.
///
/// For detailed documentation see:
/// - **[../plans/tao/enhanced-test-framework-plan.md](../plans/tao/enhanced-test-framework-plan.md)** - Implementation plan
import tao/test_parser.{type Test, Test}
import tao/test_runner.{type TestResult, type TestSummary, TestSummary, Pass, Fail, Error as TestErr, Skipped, TimedOut}
import syntax/grammar.{type Span, Span}
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
    Fail(t, expected, got, source) -> {
      case t {
        Test(name, _, _, span, _) -> {
          report_failure_with_snippet(name, expected, got, span, source)
        }
      }
    }
    TestErr(t, message, source) -> {
      case t {
        Test(name, _, _, span, _) -> {
          report_error_with_snippet(name, message, span, source)
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
    Fail(t, expected, got, source) -> {
      case t {
        Test(name, _, _, span, _) -> {
          report_failure_with_snippet(name, expected, got, span, source)
        }
      }
    }
    TestErr(t, message, source) -> {
      case t {
        Test(name, _, _, span, _) -> {
          report_error_with_snippet(name, message, span, source)
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

/// Report a test failure with source snippet.
fn report_failure_with_snippet(
  name: String,
  expected: String,
  got: String,
  span: Span,
  source: String,
) -> Nil {
  io.println("✗ FAIL: " <> name)
  
  // Show source snippet
  io.println("   ┌─ " <> span.file <> ":" <> int.to_string(span.start_line) <> ":" <> int.to_string(span.start_col))
  io.println("   │")
  
  // Get the failing line
  let lines = string.split(source, "\n")
  let line_num = span.start_line - 1
  let line_content = get_line(lines, line_num)
  
  io.println(" " <> int.to_string(span.start_line) <> " │ " <> line_content)
  io.println("   │ " <> string.repeat("^", span.end_col - span.start_col + 1))
  io.println("   │")
  io.println("   = expected: " <> expected)
  io.println("   = got:      " <> got)
  io.println("")
}

/// Report a test error with source snippet.
fn report_error_with_snippet(
  name: String,
  message: String,
  span: Span,
  source: String,
) -> Nil {
  io.println("⚠ ERROR: " <> name)
  
  // Show source snippet
  io.println("   ┌─ " <> span.file <> ":" <> int.to_string(span.start_line) <> ":" <> int.to_string(span.start_col))
  io.println("   │")
  
  // Get the error line
  let lines = string.split(source, "\n")
  let line_num = span.start_line - 1
  let line_content = get_line(lines, line_num)
  
  io.println(" " <> int.to_string(span.start_line) <> " │ " <> line_content)
  io.println("   │ " <> string.repeat("^", span.end_col - span.start_col + 1))
  io.println("   │")
  io.println("   = " <> message)
  io.println("")
}

/// Get a line from a list of lines by index.
fn get_line(lines: List(String), index: Int) -> String {
  get_line_loop(lines, index, 0)
}

fn get_line_loop(lines: List(String), index: Int, current: Int) -> String {
  case lines {
    [] -> ""
    [line, ..rest] -> {
      case current == index {
        True -> line
        False -> get_line_loop(rest, index, current + 1)
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
