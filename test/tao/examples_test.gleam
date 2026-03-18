// ============================================================================
// TAO EXAMPLES E2E TESTS
// ============================================================================
/// End-to-end tests that verify Tao example files produce expected output.
///
/// ## Directory Structure
///
/// ```
/// examples/tao/
/// ├── programs/              # Successful programs
/// │   ├── 01-basics/
/// │   │   ├── *.tao          # Source files
/// │   │   └── *.output.txt   # Expected stdout
/// │   ├── 02-functions/
/// │   ├── 03-pattern-matching/
/// │   └── 04-control-flow/
/// ├── errors/                # Examples that should fail
/// │   ├── syntax_errors/
/// │   │   ├── *.tao
/// │   │   └── *.output.txt   # Expected stderr
/// │   ├── type_errors/
/// │   ├── import_errors/
/// │   └── exhaustiveness/
/// └── features/              # Feature-specific examples
/// ```
///
/// ## Usage
///
/// Tests automatically discover all `.tao` files and verify they
/// produce the expected output based on their directory.
///
/// To add a new example:
/// 1. Create the `.tao` file in the appropriate directory
/// 2. Run the CLI to see actual output
/// 3. Copy the output to `.output.txt`
/// 4. The test will automatically pick it up
import tao/compiler.{compile_single_file, type CompileErrorType, ParseError as CompilerParseError, ImportError as CompilerImportError, CircularImport as CompilerCircularImport, ModuleNotFound as CompilerModuleNotFound}
import tao/desugar.{desugar_module}
import tao/global_context.{new_context, with_prelude}
import core/core.{type Error as TypeError, type State, initial_state, infer, eval, quote}
import core/syntax as core_syntax
import gleam/list
import gleam/result
import gleam/string
import gleam/int
import gleeunit
import gleeunit/should
import simplifile
import syntax/grammar.{type Span, Span}

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

/// Test all examples in programs/01-basics/ directory
pub fn programs_basics_test() {
  "examples/tao/programs/01-basics"
  |> discover_examples(ShouldSucceed, "programs/01-basics")
  |> run_examples
  |> should.equal([])
}

/// Test all examples in programs/02-functions/ directory
pub fn programs_functions_test() {
  "examples/tao/programs/02-functions"
  |> discover_examples(ShouldSucceed, "programs/02-functions")
  |> run_examples
  |> should.equal([])
}

/// Test all examples in programs/03-pattern-matching/ directory
pub fn programs_pattern_matching_test() {
  "examples/tao/programs/03-pattern-matching"
  |> discover_examples(ShouldSucceed, "programs/03-pattern-matching")
  |> run_examples
  |> should.equal([])
}

/// Test all examples in programs/03-test-run/ directory
pub fn programs_test_run_test() {
  "examples/tao/programs/03-test-run"
  |> discover_examples(ShouldSucceed, "programs/03-test-run")
  |> run_examples
  |> should.equal([])
}

/// Test all examples in programs/04-recursion/ directory
pub fn programs_recursion_test() {
  "examples/tao/programs/04-recursion"
  |> discover_examples(ShouldSucceed, "programs/04-recursion")
  |> run_examples
  |> should.equal([])
}

/// Test all examples in programs/05-control-flow/ directory
pub fn programs_control_flow_test() {
  "examples/tao/programs/05-control-flow"
  |> discover_examples(ShouldSucceed, "programs/05-control-flow")
  |> run_examples
  |> should.equal([])
}

/// Test all examples in programs/07-modules/ directory
pub fn programs_modules_test() {
  "examples/tao/programs/07-modules"
  |> discover_examples(ShouldSucceed, "programs/07-modules")
  |> run_examples
  |> should.equal([])
}

// TODO: Re-enable error tests when error reporting is implemented
// /// Test all examples in errors/syntax_errors/ directory
// pub fn errors_syntax_test() {
//   "examples/tao/errors/syntax_errors"
//   |> discover_examples(ShouldFail, "errors/syntax_errors")
//   |> run_examples
//   |> should.equal([])
// }

// TODO: Re-enable error tests when type checking is fully implemented
// /// Test all examples in errors/type_errors/ directory
// pub fn errors_type_test() {
//   "examples/tao/errors/type_errors"
//   |> discover_examples(ShouldFail, "errors/type_errors")
//   |> run_examples
//   |> should.equal([])
// }

// TODO: Re-enable error tests when import resolution is fully implemented
// /// Test all examples in errors/import_errors/ directory
// pub fn errors_import_test() {
//   "examples/tao/errors/import_errors"
//   |> discover_examples(ShouldFail, "errors/import_errors")
//   |> run_examples
//   |> should.equal([])
// }

// TODO: Re-enable error tests when exhaustiveness checking is implemented
// /// Test all examples in errors/exhaustiveness/ directory
// pub fn errors_exhaustiveness_test() {
//   "examples/tao/errors/exhaustiveness"
//   |> discover_examples(ShouldFail, "errors/exhaustiveness")
//   |> run_examples
//   |> should.equal([])
// }

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
      |> list.filter(fn(f) { string.ends_with(f, ".tao") })
      |> list.map(fn(filename) {
        let name = extract_name(filename)
        let path = dir <> "/" <> filename
        let output_path = path |> string.replace(".tao", ".output.txt")
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
    |> string.replace(".tao", "")
  })
  |> result.unwrap("unknown")
}

// ============================================================================
// TEST EXECUTION
// ============================================================================

fn run_examples(examples: List(Example)) -> List(String) {
  examples
  |> list.filter_map(fn(example) {
    case run_example(example) {
      True -> Ok("Example failed: " <> example.name)
      False -> Error(Nil)
    }
  })
}

/// Run a single example and return True if it failed, False if it passed
fn run_example(example: Example) -> Bool {
  let source_result = read_file("source", example.path)
  let expected_result = read_file("output", example.output_path)

  case #(source_result, expected_result) {
    #(Error(msg), _) | #(_, Error(msg)) -> {
      echo ["[file read] " <> msg]
      True
    }
    #(Ok(source), Ok(expected)) -> {
      // Compile the Tao source
      let #(ctx, module, compile_errors) = compile_single_file(example.path, source, ".")

      case #(compile_errors, example.category) {
        #([err, ..], ShouldFail) -> {
          // Expected failure - check if error message matches
          let actual_output = format_compile_errors(compile_errors, source, example.path)

          case normalize_output(actual_output) == normalize_output(expected) {
            True -> False  // Test passed
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
        #([err, ..], ShouldSucceed) -> {
          // Unexpected errors
          let msg = [
            "FAIL: " <> example.path,
            "Expected: success",
            "Got: compile errors",
            "",
            "Formatted errors:",
            format_compile_errors(compile_errors, source, example.path),
          ]
          echo msg
          True
        }
        #([], ShouldFail) -> {
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
        #([], ShouldSucceed) -> {
          // Success - desugar, type check, and evaluate
          let #(term, _dc) = desugar_module(module, ctx)

          // Run type inference
          let #(_value, _typ, state) = infer(initial_state, term)
          let type_errors = state.errors

          case type_errors {
            [] -> {
              // Evaluate and compare output
              let value = eval(initial_state.ffi, [], term)
              let span = Span("", 0, 0, 0, 0)
              let normal_form = quote(initial_state.ffi, 0, value, span)
              let actual_output = core_syntax.format(normal_form)
              
              case normalize_output(actual_output) == normalize_output(expected) {
                True -> False  // Test passed
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
            errors -> {
              // Unexpected type errors
              let msg = [
                "FAIL: " <> example.path,
                "Expected: success",
                "Got: type errors",
                "",
                "Formatted errors:",
                format_type_errors(errors, source, example.path),
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

fn format_compile_errors(errors: List(CompileErrorType), source: String, file: String) -> String {
  errors
  |> list.map(fn(err) {
    case err {
      CompilerParseError(message, span) -> {
        "Parse error: " <> message <> "\n  at " <> span.file <> ":" <> int.to_string(span.start_line) <> ":" <> int.to_string(span.start_col)
      }
      CompilerImportError(message, span) -> {
        "Import error: " <> message <> "\n  at " <> span.file <> ":" <> int.to_string(span.start_line) <> ":" <> int.to_string(span.start_col)
      }
      CompilerCircularImport(cycle, span) -> {
        "Circular import detected: " <> string.join(cycle, " -> ") <> "\n  at " <> span.file <> ":" <> int.to_string(span.start_line) <> ":" <> int.to_string(span.start_col)
      }
      CompilerModuleNotFound(path, span) -> {
        "Module not found: " <> path <> "\n  at " <> span.file <> ":" <> int.to_string(span.start_line) <> ":" <> int.to_string(span.start_col)
      }
    }
  })
  |> string.join("\n\n")
}

fn format_type_errors(errors: List(TypeError), source: String, file: String) -> String {
  // For now, just show error count
  // TODO: Use error_reporter for proper formatting
  "Type errors: " <> int.to_string(list.length(errors))
}

fn read_file(label: String, path: String) -> Result(String, String) {
  case simplifile.read(path) {
    Ok(content) -> Ok(content)
    Error(_) -> Error("[" <> label <> "] failed to read: " <> path)
  }
}

// Normalize output for comparison (just trim whitespace)
fn normalize_output(output: String) -> String {
  output |> string.trim
}
