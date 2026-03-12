/// Compiler Bootstrap CLI
///
/// Command-line interface for checking and running core/tao files.
///
/// ## Usage
///
/// ```bash
/// gleam run check path/to/file.core.tao   # Type-check
/// gleam run run path/to/file.core.tao     # Type-check and evaluate
/// gleam run --help                         # Show help
/// ```
import argv
import core/core.{type Term, type Error as TypeError, type State, initial_state, infer, eval, quote}
import core/syntax
import gleam/int
import gleam/io
import gleam/list
import gleam/string
import simplifile
import syntax/grammar.{ParseError as GrammarParseError, type ParseError as GrammarParseErrorType, Span}
import syntax/error_reporter

// ============================================================================
// TYPES
// ============================================================================

pub type Command {
  Check(file: String, verbose: Bool, debug: Bool)
  Run(file: String, verbose: Bool, debug: Bool)
  Help
}

pub type FileType {
  Core
  Tao
}

pub type File {
  File(path: String, contents: String, file_type: FileType)
}

pub type Error {
  ParseError(errors: List(String))
  TypeError(errors: List(TypeError))
  RuntimeError(message: String)
  FileNotFound(path: String)
  FileReadError(path: String, error: simplifile.FileError)
  InvalidArguments(message: String)
  UnknownCommand(command: String)
}

// ============================================================================
// Entry Point
// ============================================================================

pub fn main() {
  let args = command_line_args()

  case parse_args(args) {
    Ok(command) -> {
      case command {
        Check(file, verbose, debug) -> {
          case run_check(file, verbose, debug) {
            Ok(_) -> Nil
            Error(_) -> Nil
          }
        }
        Run(file, verbose, debug) -> {
          case run_run(file, verbose, debug) {
            Ok(_) -> Nil
            Error(_) -> Nil
          }
        }
        Help -> {
          print_help()
        }
      }
    }
    Error(msg) -> {
      io.println("Error: " <> msg)
      io.println("Run with --help for usage information")
    }
  }
}

fn command_line_args() -> List(String) {
  // Get command-line arguments using argv library
  let argv.Argv(arguments: args, ..) = argv.load()
  args
}

// ============================================================================
// ARGUMENT PARSING
// ============================================================================

fn parse_args(args: List(String)) -> Result(Command, String) {
  case args {
    [] -> Ok(Help)
    ["-h"] | ["--help"] -> Ok(Help)
    ["check", file, ..rest] -> {
      let verbose = has_flag(rest, "-v", "--verbose")
      let debug = has_flag(rest, "--debug", "--debug")
      Ok(Check(file, verbose, debug))
    }
    ["run", file, ..rest] -> {
      let verbose = has_flag(rest, "-v", "--verbose")
      let debug = has_flag(rest, "--debug", "--debug")
      Ok(Run(file, verbose, debug))
    }
    [cmd, ..] -> Error("Unknown command: " <> cmd)
  }
}

/// Check if a flag is present in argument list (supports both short and long forms)
/// 
/// Example: has_flag(["-v", "--debug"], "-v", "--verbose") -> True
fn has_flag(args: List(String), short: String, long: String) -> Bool {
  list.contains(args, short) || list.contains(args, long)
}

// ============================================================================
// HELP
// ============================================================================

fn print_help() {
  io.println("compiler-bootstrap - Core language compiler")
  io.println("")
  io.println("Usage: gleam run <command> <file>")
  io.println("")
  io.println("Commands:")
  io.println("  check <file>    Type-check a file")
  io.println("  run <file>      Type-check and evaluate a file")
  io.println("")
  io.println("Options:")
  io.println("  -h, --help      Show this help message")
  io.println("  -v, --verbose   Verbose output")
  io.println("  --debug         Debug mode (print AST and types)")
  io.println("")
  io.println("Examples:")
  io.println("  gleam run check example.core.tao")
  io.println("  gleam run run example.core.tao")
  io.println("  gleam run check --verbose example.core.tao")
}

// ============================================================================
// FILE LOADING
// ============================================================================

/// Load a file from disk using simplifile
fn load_file(path: String) -> Result(File, Error) {
  let file_type = detect_file_type(path)

  case simplifile.read(from: path) {
    Ok(contents) -> Ok(File(path, contents, file_type))
    Error(simplifile.Enoent) -> Error(FileNotFound(path))
    Error(err) -> Error(FileReadError(path, err))
  }
}

fn detect_file_type(path: String) -> FileType {
  case string.ends_with(path, ".core.tao") {
    True -> Core
    False -> {
      case string.ends_with(path, ".tao") {
        True -> Tao
        False -> Core  // Default to core for unknown extensions
      }
    }
  }
}

// ============================================================================
// CHECK COMMAND
// ============================================================================

fn run_check(file: String, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  case verbose {
    True -> io.println("✓ Loading " <> file)
    False -> Nil
  }

  let file_result = load_file(file)
  case file_result {
    Error(err) -> {
      report_error(err)
      Error(err)
    }
    Ok(f) -> {
      case verbose {
        True -> io.println("✓ Detected file type: " <> file_type_to_string(f.file_type))
        False -> Nil
      }

      case f.file_type {
        Core -> check_core(f, verbose, debug)
        Tao -> check_tao(f, verbose, debug)
      }
    }
  }
}

fn check_core(file: File, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  case verbose {
    True -> io.println("✓ Parsing...")
    False -> Nil
  }

  let parse_result = syntax.parse(file.contents)

  case parse_result.errors {
    [err, ..] -> {
      // Report parse errors with source snippets
      io.println("")
      let diagnostic = error_reporter.parse_error_to_diagnostic(err, file.contents, file.path)
      io.println(error_reporter.format_diagnostic(diagnostic, file.contents))
      io.println("")
      Error(ParseError(parse_result.errors |> list.map(format_parse_error)))
    }
    [] -> {
      case debug {
        True -> {
          io.println("AST:")
          io.println(debug_term(parse_result.ast))
        }
        False -> Nil
      }

      case verbose {
        True -> {
          io.println("✓ Parsed successfully")
          io.println("✓ Type checking...")
        }
        False -> Nil
      }

      // Run type checker
      let #(_type_result, _type_annotation, final_state) = infer(initial_state, parse_result.ast)

      case final_state.errors {
        [_err, ..] -> {
          // Report type errors with source snippets
          io.println("")
          final_state.errors |> list.each(fn(e) {
            let diagnostic = error_reporter.type_error_to_diagnostic(e, file.contents, file.path)
            io.println(error_reporter.format_diagnostic(diagnostic, file.contents))
          })
          io.println("")
          Error(TypeError(final_state.errors))
        }
        [] -> {
          io.println("✓ Type checking " <> file.path)
          io.println("✓ No errors found")
          Ok(Nil)
        }
      }
    }
  }
}

fn format_parse_error(err: GrammarParseErrorType) -> String {
  case err {
    GrammarParseError(span: span, expected: exp, got: g, context: ctx) ->
      "Parse error" <> case ctx {
        "" -> ""
        _ -> " in " <> ctx
      } <> ": expected " <> exp <> ", got " <> g
  }
}

fn check_tao(file: File, _verbose: Bool, _debug: Bool) -> Result(Nil, Error) {
  // Tao support not yet implemented
  io.println("✗ Tao language support not yet implemented")
  io.println("  File: " <> file.path)
  Error(RuntimeError("Tao not implemented"))
}

// ============================================================================
// RUN COMMAND
// ============================================================================

fn run_run(file: String, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  case verbose {
    True -> io.println("✓ Loading " <> file)
    False -> Nil
  }

  let file_result = load_file(file)
  case file_result {
    Error(err) -> {
      report_error(err)
      Error(err)
    }
    Ok(f) -> {
      case verbose {
        True -> io.println("✓ Detected file type: " <> file_type_to_string(f.file_type))
        False -> Nil
      }

      case f.file_type {
        Core -> run_core(f, verbose, debug)
        Tao -> run_tao(f, verbose, debug)
      }
    }
  }
}

fn run_core(file: File, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  case verbose {
    True -> io.println("✓ Parsing...")
    False -> Nil
  }

  let parse_result = syntax.parse(file.contents)

  case parse_result.errors {
    [err, ..] -> {
      io.println("✗ Parse error:")
      io.println(format_parse_error(err))
      Error(ParseError(parse_result.errors |> list.map(format_parse_error)))
    }
    [] -> {
      case debug {
        True -> {
          io.println("AST:")
          io.println(debug_term(parse_result.ast))
        }
        False -> Nil
      }

      case verbose {
        True -> {
          io.println("✓ Parsed successfully")
          io.println("✓ Type checking...")
        }
        False -> Nil
      }

      // Run type checker
      let #(_type_result, _type_annotation, type_state) = infer(initial_state, parse_result.ast)

      case type_state.errors {
        [_err, ..] -> {
          // Report type errors with source snippets
          io.println("")
          type_state.errors |> list.each(fn(e) {
            let diagnostic = error_reporter.type_error_to_diagnostic(e, file.contents, file.path)
            io.println(error_reporter.format_diagnostic(diagnostic, file.contents))
          })
          io.println("")
          Error(TypeError(type_state.errors))
        }
        [] -> {
          io.println("✓ Type checking " <> file.path)
          io.println("✓ Evaluating...")

          // Evaluate the term
          let env = []
          let ffi = initial_state.ffi
          let value = eval(ffi, env, parse_result.ast)

          // Quote back to normal form
          let span = Span("", 0, 0, 0, 0)
          let normal_form = quote(ffi, 0, value, span)

          // Format and print the result
          let formatted = syntax.format(normal_form)
          io.println("Result: " <> formatted)
          Ok(Nil)
        }
      }
    }
  }
}

fn run_tao(file: File, _verbose: Bool, _debug: Bool) -> Result(Nil, Error) {
  // Tao support not yet implemented
  io.println("✗ Tao language support not yet implemented")
  io.println("  File: " <> file.path)
  Error(RuntimeError("Tao not implemented"))
}

// ============================================================================
// ERROR REPORTING
// ============================================================================

/// Report an error to stderr with consistent formatting
fn report_error(error: Error) {
  case error {
    ParseError(errors) -> {
      io.println("Parse error:")
      errors |> list.each(fn(e) { io.println("  " <> e) })
    }
    TypeError(_errors) -> {
      io.println("Type error:")
      io.println("  See above for details")
    }
    RuntimeError(message) -> {
      io.println("Runtime error:")
      io.println("  " <> message)
    }
    FileNotFound(path) -> {
      io.println("File not found: " <> path)
    }
    FileReadError(path, err) -> {
      io.println("Failed to read file: " <> path)
      io.println("  Reason: " <> format_file_error(err))
    }
    InvalidArguments(message) -> {
      io.println("Invalid arguments: " <> message)
    }
    UnknownCommand(command) -> {
      io.println("Unknown command: " <> command)
    }
  }
}

/// Format a file error to a human-readable message
fn format_file_error(err: simplifile.FileError) -> String {
  case err {
    simplifile.Enoent -> "File not found"
    simplifile.Eacces -> "Permission denied"
    simplifile.Eexist -> "File already exists"
    simplifile.Eisdir -> "Is a directory"
    simplifile.Enametoolong -> "Filename too long"
    simplifile.Enospc -> "No space left on device"
    simplifile.Enotdir -> "Not a directory"
    simplifile.Eio -> "I/O error"
    simplifile.NotUtf8 -> "File is not valid UTF-8"
    _ -> "Unknown error"
  }
}

// ============================================================================
// DEBUG OUTPUT
// ============================================================================

fn debug_term(term: Term) -> String {
  // Simple debug representation
  // In a full implementation, this would pretty-print the AST
  syntax.format(term)
}

fn file_type_to_string(file_type: FileType) -> String {
  case file_type {
    Core -> "Core language (.core.tao)"
    Tao -> "Tao high-level language (.tao)"
  }
}
