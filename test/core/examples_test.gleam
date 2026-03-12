// ============================================================================
// E2E TESTS FOR COMPILER BOOTSTRAP
// ============================================================================
/// End-to-end tests that verify example files compile correctly.
///
/// ## Directory Structure
///
/// ```
/// examples/core/
/// ├── programs/           # Successful programs
/// │   ├── *.core.tao      # Source files
/// │   └── *.output.txt    # Expected: "OK"
/// ├── terms/              # Term examples (successful)
/// │   ├── *.core.tao
/// │   └── *.output.txt    # Expected: "OK"
/// └── errors/             # Examples that should fail
///     ├── type_errors/
///     │   ├── *.core.tao
///     │   └── *.output.txt  # Expected: "ERROR"
///     └── ...
/// ```
///
/// ## Usage
///
/// Tests automatically discover all `.core.tao` files and verify they
/// succeed or fail as expected based on their directory.
///
/// To add a new example:
/// 1. Create the `.core.tao` file in the appropriate directory
/// 2. Create a `.output.txt` file with "OK" (for success) or "ERROR" (for failure)
/// 3. The test will automatically pick it up
import core/core.{infer, initial_state}
import core/syntax
import gleam/list
import gleam/result
import gleam/string
import gleeunit
import gleeunit/should
import simplifile

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
  list.filter(examples, run_example)
}

// Prints errors and debugging info to stdout with echo.
// Returns:
// - True to report this example failed.
// - False to acknowledge everything went as expected.
fn run_example(example: Example) -> Bool {
  use source <- result.try(read_file("source", example.path))
  use expected <- result.try(read_file("output", example.output_path))
  let parse_result = syntax.parse(source)
  let #(term, syntax_errors) = #(parse_result.ast, parse_result.errors)
  let #(result, typ, s) = infer(initial_state, term)
  let errors = list.append(syntax_errors, s.errors)
  case #(example.category, errors) {
    #(ShouldSucceed, []) -> {
      todo as "check result against expected output"
      False
    }
    #(ShouldSucceed, errors) -> {
      let msg = [
        "[ShouldSucceed] " <> example.path,
        "Got errors:",
        string.join(list.map(errors, fn(e) { "- " <> e }), "\n"),
      ]
      echo msg
      True
    }
    #(ShouldFail, []) -> {
      let msg = [
        "[ShouldFail] " <> example.path,
        "Expected this to fail with errors, but it succeeded.",
      ]
      echo msg
      True
    }
    #(ShouldFail, errors) -> {
      todo as "should compare the actual error messages and make sure they match the expected output"
      False
    }
  }

  case example.category {
    ShouldSucceed -> {
      case parse_result.errors {
        [first_error, ..] -> {
          let msg = [
            "FAIL: " <> example.path,
            "Expected: parse and type-check successfully",
            "Got: parse errors",
            "First error: " <> string.inspect(first_error),
          ]
          Error(string.join(msg, "\n"))
        }
        [] -> {
          // Parse succeeded - check type-check
          let #(_type_result, _type_annotation, final_state) =
            infer(initial_state, parse_result.ast)

          case final_state.errors {
            [first_error, ..] -> {
              // Type-check failed - report error
              let msg = [
                "FAIL: " <> example.path,
                "Expected: type-check successfully",
                "Got: type errors",
                "First error: " <> string.inspect(first_error),
              ]
              Error(string.join(msg, "\n"))
            }
            [] -> {
              // Success! Check expected output is "OK"
              case string.trim(expected) {
                "OK" -> Ok(Nil)
                other -> {
                  let msg = [
                    "FAIL: " <> example.path,
                    "Expected output file to contain 'OK'",
                    "Got: " <> other,
                  ]
                  Error(string.join(msg, "\n"))
                }
              }
            }
          }
        }
      }
    }
    ShouldFail -> {
      // For error examples, check that either parse or type-check fails
      case parse_result.errors {
        _ -> {
          // Parse failed - this is expected for syntax errors
          // Check expected output is "ERROR"
          case string.trim(expected) {
            "ERROR" -> Ok(Nil)
            other -> {
              let msg = [
                "FAIL: " <> example.path,
                "Expected output file to contain 'ERROR'",
                "Got: " <> other,
              ]
              Error(string.join(msg, "\n"))
            }
          }
        }
        [] -> {
          // Parse succeeded - check type-check fails
          let #(_type_result, _type_annotation, final_state) =
            infer(initial_state, parse_result.ast)

          case final_state.errors {
            _ -> {
              // Type-check failed - this is expected for type errors
              // Check expected output is "ERROR"
              case string.trim(expected) {
                "ERROR" -> Ok(Nil)
                other -> {
                  let msg = [
                    "FAIL: " <> example.path,
                    "Expected output file to contain 'ERROR'",
                    "Got: " <> other,
                  ]
                  Error(string.join(msg, "\n"))
                }
              }
            }
            [] -> {
              // Both parse and type-check succeeded - this is wrong for error examples
              let msg = [
                "FAIL: " <> example.path,
                "Expected: parse or type-check to fail",
                "Got: both succeeded",
                "This example should be in errors/ but compiles successfully!",
              ]
              Error(string.join(msg, "\n"))
            }
          }
        }
      }
    }
  }
}

fn read_file(label: String, path: String) -> Result(String, String) {
  case simplifile.read(path) {
    Ok(content) -> Ok(content)
    Error(_) -> Error("[" <> label <> "] failed to read: " <> path)
  }
}
