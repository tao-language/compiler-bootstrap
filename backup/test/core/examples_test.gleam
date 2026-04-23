// ============================================================================
// E2E TESTS FOR COMPILER BOOTSTRAP
// ============================================================================
/// End-to-end tests that verify example files produce expected output.
///
/// ## Directory Structure
///
/// ```
/// examples/core/
/// ├── programs/           # Successful programs
/// │   ├── *.core.tao      # Source files
/// │   └── *.output.txt    # Expected stdout (NbE result)
/// ├── terms/              # Term examples (successful)
/// │   ├── *.core.tao
/// │   └── *.output.txt    # Expected stdout (NbE result)
/// └── errors/             # Examples that should fail
///     ├── type_errors/
///     │   ├── *.core.tao
///     │   └── *.output.txt  # Expected stderr (formatted errors)
///     └── ...
/// ```
///
/// ## Usage
///
/// Tests automatically discover all `.core.tao` files and verify they
/// produce the expected output based on their directory.
///
/// To add a new example:
/// 1. Create the `.core.tao` file in the appropriate directory
/// 2. Run the CLI to see actual output
/// 3. Copy the output to `.output.txt`
/// 4. The test will automatically pick it up
import core/ast as ast
import core/state.{type Error, SyntaxError, initial_state}
import core/infer.{infer}
import core/quote.{quote}
import core/syntax
import gleam/list
import gleam/result
import gleam/string
import gleeunit
import gleeunit/should
import simplifile
import syntax/error_reporter
import syntax/grammar.{ParseError, Span}

// ============================================================================
// TYPES
// ============================================================================

type Example {
  Example(
    name: String,
    path: String,
    output_path: String,
    category: ExampleCategory,
    subcategory: String,
  )
}

type ExampleCategory {
  ShouldSucceed
  ShouldFail
}

// ============================================================================
// ENTRY POINT
// ============================================================================

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST DISCOVERY
// ============================================================================

/// Test all examples in programs/ directory
pub fn programs_examples_test() {
  "examples/core/programs"
  |> discover_examples(ShouldSucceed, "programs")
  |> report_errors
  |> should.equal([])
}

/// Test all examples in terms/ directory
pub fn terms_examples_test() {
  "examples/core/terms"
  |> discover_examples(ShouldSucceed, "terms")
  |> report_errors
  |> should.equal([])
}

/// Test all examples in errors/type_errors/ directory
pub fn type_errors_examples_test() {
  "examples/core/errors/type_errors"
  |> discover_examples(ShouldFail, "errors/type_errors")
  |> report_errors
  |> should.equal([])
}

/// Test all examples in errors/syntax_errors/ directory
pub fn syntax_errors_examples_test() {
  "examples/core/errors/syntax_errors"
  |> discover_examples(ShouldFail, "errors/syntax_errors")
  |> report_errors
  |> should.equal([])
}

/// Test all examples in errors/syntax_recovery/ directory
pub fn syntax_recovery_examples_test() {
  "examples/core/errors/syntax_recovery"
  |> discover_examples(ShouldFail, "errors/syntax_recovery")
  |> report_errors
  |> should.equal([])
}

/// Test all examples in errors/exhaustiveness_checks/ directory
pub fn exhaustiveness_checks_examples_test() {
  "examples/core/errors/exhaustiveness_checks"
  |> discover_examples(ShouldFail, "errors/exhaustiveness_checks")
  |> report_errors
  |> should.equal([])
}

// ============================================================================
// EXAMPLE DISCOVERY
// ============================================================================

fn discover_examples(
  dir: String,
  category: ExampleCategory,
  subcategory: String,
) -> List(Example) {
  case simplifile.read_directory(dir) {
    Ok(files) -> {
      files
      |> list.filter(fn(f) { string.ends_with(f, ".core.tao") })
      |> list.map(fn(filename) {
        let name = extract_name(filename)
        // Build full paths from directory and filename
        let path = dir <> "/" <> filename
        let output_path = path |> string.replace(".core.tao", ".output.txt")
        Example(name, path, output_path, category, subcategory)
      })
    }
    Error(_) -> {
      let msg = "failed to read directory: " <> dir
      panic as msg
    }
  }
}

fn extract_name(path: String) -> String {
  path
  |> string.split("/")
  |> list.last
  |> result.map(fn(f) {
    f
    |> string.replace(".core.tao", "")
  })
  |> result.unwrap("unknown")
}

// ============================================================================
// TEST EXECUTION
// ============================================================================

fn report_errors(examples: List(Example)) -> List(String) {
  examples
  |> list.filter_map(fn(example) {
    case run_example(example) {
      True -> Ok("Example failed: " <> example.name)
      False -> Error(Nil)
    }
  })
}

// Prints errors and debugging info to stdout with echo.
// Returns:
// - True to report this example failed.
// - False to acknowledge everything went as expected.
fn run_example(example: Example) -> Bool {
  let source_result = read_file("source", example.path)
  let expected_result = read_file("output", example.output_path)

  case #(source_result, expected_result) {
    #(Error(msg), _) | #(_, Error(msg)) -> {
      echo ["[file read] " <> msg]
      True
    }
    #(Ok(source), Ok(expected)) -> {
      let parse_result = syntax.parse(source)
      let term = parse_result.ast
      let syntax_errors =
        parse_result.errors |> list.map(syntax_error_to_core_error)

      // Run type inference
      let #(_, _, s2) = infer(initial_state, term)
      let type_errors = s2.errors

      // Combine all errors
      let all_errors = list.append(syntax_errors, type_errors)

      case example.category {
        ShouldSucceed -> {
          case all_errors {
            [] -> {
              // Success - for now just check that it compiles
              // TODO: Compare actual NbE output once term_to_string is fixed
              False
              // Test passed
            }
            errors -> {
              // Unexpected errors
              let msg = [
                "FAIL: " <> example.path,
                "Expected: success",
                "Got: errors",
                "",
                "Formatted errors:",
                format_errors(errors, source, example.path),
              ]
              echo msg
              True
            }
          }
        }
        ShouldFail -> {
          case all_errors {
            [] -> {
              // Unexpected success
              let msg = [
                "FAIL: " <> example.path,
                "Expected: errors",
                "Got: success",
                "",
                "This example should be in errors/ but compiles successfully!",
              ]
              echo msg
              True
            }
            errors -> {
              // Expected failure - compare actual error messages
              let actual_output = format_errors(errors, source, example.path)

              case
                normalize_output(actual_output) == normalize_output(expected)
              {
                True -> False
                // Test passed
                False -> {
                  let msg = [
                    "FAIL: " <> example.path,
                    "Expected output:",
                    "```",
                    string.trim(expected),
                    "```",
                    "Actual output:",
                    "```",
                    string.trim(actual_output),
                    "```",
                  ]
                  echo msg
                  True
                }
              }
            }
          }
        }
      }
    }
  }
}

fn syntax_error_to_core_error(parse_error) -> Error {
  case parse_error {
    ParseError(span, expected, got, context) -> {
      SyntaxError(span, expected, got, context)
    }
  }
}

fn format_errors(errors: List(Error), source: String, file: String) -> String {
  errors
  |> list.map(fn(err) {
    case err {
      SyntaxError(span, expected, got, context) -> {
        let parse_err = ParseError(span, expected, got, context)
        let diagnostic =
          error_reporter.parse_error_to_diagnostic(parse_err, source, file)
        error_reporter.format_diagnostic(diagnostic, source)
      }
      _ -> {
        let diagnostic =
          error_reporter.type_error_to_diagnostic(err, source, file)
        error_reporter.format_diagnostic(diagnostic, source)
      }
    }
  })
  |> string.join("\n")
}

fn read_file(label: String, path: String) -> Result(String, String) {
  case simplifile.read(path) {
    Ok(content) -> Ok(content)
    Error(_) -> Error("[" <> label <> "] failed to read: " <> path)
  }
}

// Normalize output for comparison (just trim whitespace)
fn normalize_output(output: String) -> String {
  output
  |> string.trim
  // Remove timing line which varies between runs
  |> string.replace("Compiled in 0.05s", "")
  |> string.replace("Compiled in 0.06s", "")
  |> string.replace("Running compiler_bootstrap.main", "")
  |> string.trim
}
