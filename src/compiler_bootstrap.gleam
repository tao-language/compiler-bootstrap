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
import core/ast as ast
import core/state.{type Error as TypeError, State, type State, initial_state, initial_state_with, SyntaxError, TypeMismatch, CtrUndefined, VarUndefined, MatchMissingCase, MatchRedundantCase}
import tao/ffi.{tao_ffis}
import core/infer.{infer}
import core/eval.{eval_from_state}
import core/quote.{quote}
import core/subst.{force}
import core/syntax as core_syntax
import syntax/error_reporter
import tao/syntax.{parse as tao_parse, get_expr_span, type Expr as TaoExpr, Var as TaoVar, Int as TaoInt, Float as TaoFloat, BinOp as TaoBinOp, UnaryOp as TaoUnaryOp, OverloadedFn as TaoOverloadedFn, OverloadedApp as TaoOverloadedApp, Let as TaoLet, Block as TaoBlockExpr, SimpleFn as TaoSimpleFn, App as TaoApp, Lambda as TaoLambda, Match as TaoMatch, Str as TaoStr, Test as TaoTest, Run as TaoRun, If as TaoIf, For, While, Loop, Break, Continue, Import, Ctr, TypeDecl, expr_to_ast}
import tao/desugar.{desugar_module}
import tao/global_context.{new_context, with_prelude, set_current_module}
import tao/compiler.{compile_files, compile_single_file, type CompileResult, type CompileErrorType, ParseError as CompilerParseError, ImportError as CompilerImportError, CircularImport as CompilerCircularImport, ModuleNotFound as CompilerModuleNotFound}
import tao/ast as tao_ast
import syntax/grammar.{ParseError as GrammarParseError, type ParseError as GrammarParseErrorType, type Span, Span}
import tao/test_api.{run_test_file, calculate_summary, all_passed, get_failures, type TestResult, strip_test_lines}
import tao/test_reporter.{report_results, report_final_status, list_test_expressions}
import gleam/int
import gleam/io
import gleam/list
import gleam/string
import gleam/option.{Some, None}
import simplifile
import exit_code

// ============================================================================
// TYPES
// ============================================================================

pub type Command {
  Check(file: String, verbose: Bool, debug: Bool)
  Run(file: String, verbose: Bool, debug: Bool)
  Test(paths: List(String), match_pattern: String, list_tests: Bool, verbose: Bool, debug: Bool)
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
  CompileError(errors: List(CompileErrorType))
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
        Test(paths, match_pattern, list_tests, verbose, debug) -> {
          case run_test_command(paths, match_pattern, list_tests, verbose, debug) {
            True -> Nil
            False -> exit_code.exit(1)
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
    ["test", ..rest] -> {
      let paths = get_paths(rest)
      let match_pattern = get_option_value(rest, "--match", "-m") |> option.unwrap("")
      let list_tests = has_flag(rest, "--list", "-l")
      let verbose = has_flag(rest, "-v", "--verbose")
      let debug = has_flag(rest, "--debug", "--debug")
      Ok(Test(paths, match_pattern, list_tests, verbose, debug))
    }
    [cmd, ..] -> Error("Unknown command: " <> cmd)
  }
}

/// Get positional arguments (paths) from argument list
fn get_paths(args: List(String)) -> List(String) {
  list.filter(args, fn(arg) {
    string.starts_with(arg, "-") == False
  })
}

/// Get value for an option (e.g., --match "pattern")
fn get_option_value(args: List(String), long: String, short: String) -> option.Option(String) {
  find_option_value(args, long, short, False)
}

fn find_option_value(
  args: List(String),
  long: String,
  short: String,
  found_flag: Bool,
) -> option.Option(String) {
  case args {
    [] -> None
    [flag, value, ..rest] if flag == long || flag == short -> {
      case found_flag {
        True -> Some(value)
        False -> find_option_value(rest, long, short, False)
      }
    }
    [flag, ..rest] if flag == long || flag == short -> {
      find_option_value(rest, long, short, True)
    }
    [_, ..rest] -> find_option_value(rest, long, short, found_flag)
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
  io.println("Usage: gleam run <command> [options] [paths...]")
  io.println("")
  io.println("Commands:")
  io.println("  check <file>    Type-check a file")
  io.println("  run <file>      Type-check and evaluate a file")
  io.println("  test [paths]    Run tests in files or directories (default: current directory)")
  io.println("")
  io.println("Test Options:")
  io.println("  -m, --match <pattern>   Filter tests by name pattern (wildcards supported)")
  io.println("  -l, --list              List all tests without running")
  io.println("  -v, --verbose           Verbose output")
  io.println("  --debug                 Debug mode (print AST and types)")
  io.println("")
  io.println("Examples:")
  io.println("  gleam run check example.core.tao")
  io.println("  gleam run run example.core.tao")
  io.println("  gleam run test                    # Run all tests in current directory")
  io.println("  gleam run test lib/prelude/       # Run tests in a directory")
  io.println("  gleam run test file.tao           # Run tests in a file")
  io.println("  gleam run test --match \"* addition\"")
  io.println("  gleam run test --list")
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
// TEST COMMAND
// ============================================================================

/// Result of processing a single test file.
type FileTestResult {
  FileTestResult(
    path: String,
    errors: List(TypeError),
    results: List(TestResult),
    stripped_source: String,
  )
}

fn run_test_command(
  paths: List(String),
  _match_pattern: String,
  list_tests: Bool,
  verbose: Bool,
  _debug: Bool,
) -> Bool {
  let test_paths = case paths {
    [] -> ["."]
    _ -> paths
  }

  let all_file_results = collect_and_run_tests_from_paths(test_paths, verbose)

  let has_errors = list.any(all_file_results, fn(f) {
    list.length(f.errors) > 0
  })

  case has_errors {
    True -> {
      list.each(all_file_results, fn(file_result) {
        case file_result.errors {
          [] -> Nil
          [_, ..] -> {
            io.println("")
            io.println("═══ Errors in " <> file_result.path <> " ═══")
            io.println("")
            // Use stripped_source for error formatting (AST spans are from stripped source)
            let source = file_result.stripped_source
            list.each(file_result.errors, fn(e) {
              let diagnostic = error_reporter.type_error_to_diagnostic(e, source, file_result.path)
              io.println(error_reporter.format_diagnostic(diagnostic, source))
            })
            io.println("")
          }
        }
      })
      io.println("✗ Some files had errors")
      False
    }
    False -> {
      let all_results = list.flat_map(all_file_results, fn(f) { f.results })
      let summary = calculate_summary(all_results)

      case list_tests {
        True -> {
          list_test_expressions(all_results)
          True
        }
        False -> {
          io.println("")
          report_results(all_results, summary, verbose)
          report_final_status(all_passed(all_results))
          all_passed(all_results)
        }
      }
    }
  }
}

fn collect_and_run_tests_from_paths(paths: List(String), verbose: Bool) -> List(FileTestResult) {
  list.flat_map(paths, fn(path) {
    collect_and_run_tests_from_path(path, verbose)
  })
}

fn collect_and_run_tests_from_path(path: String, verbose: Bool) -> List(FileTestResult) {
  case simplifile.read(from: path) {
    Ok(contents) -> {
      case verbose {
        True -> io.println("✓ Testing " <> path)
        False -> Nil
      }
      let #(errors, results) = run_test_file(contents, path)
      let stripped = strip_test_lines(contents)
      [FileTestResult(path, errors, results, stripped)]
    }
    Error(_) -> collect_and_run_tests_from_directory(path, verbose)
  }
}

fn collect_and_run_tests_from_directory(dir_path: String, verbose: Bool) -> List(FileTestResult) {
  case simplifile.get_files(in: dir_path) {
    Ok(files) -> {
      let tao_files = list.filter(files, fn(f) { string.ends_with(f, ".tao") })
      list.flat_map(tao_files, fn(file) {
        case simplifile.read(from: file) {
          Ok(contents) -> {
            case verbose {
              True -> io.println("✓ Testing " <> file)
              False -> Nil
            }
            let #(errors, results) = run_test_file(contents, file)
            let stripped = strip_test_lines(contents)
            [FileTestResult(file, errors, results, stripped)]
          }
          Error(_) -> []
        }
      })
    }
    Error(_) -> {
      case verbose {
        True -> io.println("⚠ Could not read directory: " <> dir_path)
        False -> Nil
      }
      []
    }
  }
}

fn format_core_error(error: TypeError) -> String {
  case error {
    SyntaxError(_, expected, got, _) ->
      "Syntax error: expected " <> expected <> ", got " <> got
    TypeMismatch(_, _, _, _) ->
      "Type error: type mismatch"
    CtrUndefined(name, _) ->
      "Constructor error: undefined constructor '" <> name <> "'"
    VarUndefined(_, _) ->
      "Variable error: undefined variable"
    MatchMissingCase(_, _) ->
      "Exhaustiveness error: missing case in pattern match"
    MatchRedundantCase(_) ->
      "Warning: redundant case in pattern match"
    _ -> "Error (see above for details)"
  }
}

/// Update State.ctrs with constructor definitions from desugaring.
fn update_state_ctrs(state: State, ctrs: ast.CtrEnv) -> State {
  State(..state, ctrs: ctrs)
}

/// Evaluate and quote a Core term, printing the formatted result.
/// On success, returns the formatted string.
/// On error, reports errors to stdout and returns an empty string.
fn run_and_evaluate(
  term: ast.Term,
  type_state: State,
  source: String,
  file: String,
  verbose: Bool,
) -> Result(String, List(TypeError)) {
  // Evaluate the term (even with errors, for debugging)
  case verbose {
    True -> io.println("✓ Evaluating...")
    False -> Nil
  }

  let env = []
  let ffi = tao_ffis()
  let eval_state = initial_state_with(ffi, "True")
  let value = eval_from_state(eval_state, env, term)
  // Force the value with the substitution from type checking to solve any holes
  let forced_value = force(ffi, type_state.subst, value)

  // Quote back to normal form
  let normal_form = quote(ffi, 0, forced_value, Span(file, 0, 0, 0, 0))

  // Format and print the result
  let formatted = core_syntax.format(normal_form)

  case type_state.errors {
    [_, ..] -> {
      // Report errors
      io.println("")
      io.println("-----------------------------------------------------------")
      io.println(formatted)
      Error(type_state.errors)
    }
    [] -> {
      io.println(formatted)
      Ok(formatted)
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

  let parse_result = core_syntax.parse(file.contents)

  case parse_result.errors {
    [err, ..] -> {
      // Report parse errors
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
          // Report type errors
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
    GrammarParseError(span: _span, expected: exp, got: g, context: ctx) ->
      "Parse error" <> case ctx {
        "" -> ""
        _ -> " in " <> ctx
      } <> ": expected " <> exp <> ", got " <> g
  }
}

fn check_tao(file: File, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  case verbose {
    True -> io.println("✓ Parsing Tao...")
    False -> Nil
  }

  // Strip test lines before compiling
  let code_only = strip_test_lines(file.contents)

  // Use multi-file compiler (single file mode)
  let #(ctx, module, compile_errors) = compile_single_file(file.path, code_only, ".")

  case compile_errors {
    [err, ..] -> {
      // Report compile errors
      io.println("")
      report_compile_error(err, code_only, file.path)
      io.println("")
      Error(CompileError(compile_errors))
    }
    [] -> {
      case verbose {
        True -> {
          io.println("✓ Parsed Tao successfully")
          io.println("✓ Desugaring to Core...")
        }
        False -> Nil
      }

      // Desugar Tao to Core
      let #(term, dc) = desugar_module(module, ctx)

      case debug {
        True -> {
          io.println("Core term:")
          io.println(debug_term(term))
        }
        False -> Nil
      }

      case verbose {
        True -> io.println("✓ Desugared to Core")
        False -> Nil
      }

      // Run type checker on Core term
      // Use FFI from Tao language config for annotation evaluation
      let state_with_ffi = initial_state_with(tao_ffis(), "True")
      let state_with_ctrs = state_with_ffi |> update_state_ctrs(dc.ctrs)
      let #(_type_result, _type_annotation, final_state) = infer(state_with_ctrs, term)

      case final_state.errors {
        [_err, ..] -> {
          // Report type errors
          // Use code_only (stripped source) since AST spans were computed from it
          io.println("")
          final_state.errors |> list.each(fn(e) {
            let diagnostic = error_reporter.type_error_to_diagnostic(e, code_only, file.path)
            io.println(error_reporter.format_diagnostic(diagnostic, code_only))
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

  let parse_result = core_syntax.parse(file.contents)
  let parse_errors = parse_result.errors

  // Handle parse errors
  case parse_errors {
    [_err, ..] -> {
      io.println("")
      parse_errors |> list.each(fn(err) {
        let diagnostic = error_reporter.parse_error_to_diagnostic(err, file.contents, file.path)
        io.println(error_reporter.format_diagnostic(diagnostic, file.contents))
      })
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
        True -> io.println("✓ Parsed successfully")
        False -> Nil
      }
    }
  }

  // Run type checker (even if parse errors exist, for error accumulation)
  case verbose {
    True -> io.println("✓ Type checking...")
    False -> Nil
  }

  let #(_type_result, _type_annotation, type_state) = infer(initial_state, parse_result.ast)

  // Report type errors
  case type_state.errors {
    [_err, ..] -> {
      io.println("")
      type_state.errors |> list.each(fn(e) {
        let diagnostic = error_reporter.type_error_to_diagnostic(e, file.contents, file.path)
        io.println(error_reporter.format_diagnostic(diagnostic, file.contents))
      })
    }
    [] -> {
      case verbose {
        True -> io.println("✓ Type checking " <> file.path)
        False -> Nil
      }
    }
  }

  // Evaluate and quote the result
  case run_and_evaluate(parse_result.ast, type_state, file.contents, file.path, verbose) {
    Ok(_) -> Ok(Nil)
    Error(errors) -> Error(TypeError(errors))
  }
}

fn run_tao(file: File, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  case verbose {
    True -> io.println("✓ Parsing Tao...")
    False -> Nil
  }

  let parse_result = tao_parse(file.contents)
  let parse_errors = parse_result.errors

  // Handle parse errors
  case parse_errors {
    [_err, ..] -> {
      io.println("")
      parse_errors |> list.each(fn(err) {
        let diagnostic = error_reporter.parse_error_to_diagnostic(err, file.contents, file.path)
        io.println(error_reporter.format_diagnostic(diagnostic, file.contents))
      })
    }
    [] -> {
      case debug {
        True -> io.println("Tao AST parsed successfully")
        False -> Nil
      }
      case verbose {
        True -> io.println("✓ Parsed Tao successfully")
        False -> Nil
      }
    }
  }

  // Desugar Tao to Core (even if parse errors exist, for error accumulation)
  case verbose {
    True -> io.println("✓ Desugaring to Core...")
    False -> Nil
  }

  // Convert parsed expressions to Module
  let module = tao_ast.Module(
    path: file.path,
    body: exprs_to_stmts([parse_result.ast]),
    span: get_expr_span(parse_result.ast),
  )

  let ctx = new_context() |> with_prelude() |> set_current_module(file.path)
  let #(term, dc) = desugar_module(module, ctx)

  case debug {
    True -> {
      io.println("Core term:")
      io.println(debug_term(term))
    }
    False -> Nil
  }

  // Run type checker (with FFI for annotation evaluation)
  case verbose {
    True -> io.println("✓ Type checking...")
    False -> Nil
  }

  let initial_state_with_ctrs = initial_state_with(tao_ffis(), "True") |> update_state_ctrs(dc.ctrs)
  let #(_type_result, _type_annotation, type_state) = infer(initial_state_with_ctrs, term)

  // Report type errors
  case type_state.errors {
    [_err, ..] -> {
      io.println("")
      type_state.errors |> list.each(fn(e) {
        let diagnostic = error_reporter.type_error_to_diagnostic(e, file.contents, file.path)
        io.println(error_reporter.format_diagnostic(diagnostic, file.contents))
      })
    }
    [] -> {
      case verbose {
        True -> io.println("✓ Type checking " <> file.path)
        False -> Nil
      }
    }
  }

  // Evaluate and quote the result
  case run_and_evaluate(term, type_state, file.contents, file.path, verbose) {
    Ok(_) -> Ok(Nil)
    Error(errors) -> Error(TypeError(errors))
  }
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
    CompileError(_errors) -> {
      io.println("Compile error:")
      io.println("  See above for details")
    }
  }
}

/// Report a compile error to stderr
fn report_compile_error(error: CompileErrorType, source: String, path: String) {
  case error {
    CompilerParseError(message, span) -> {
      // Create a grammar ParseError from the compiler error so we can use full diagnostics
      let grammar_error = GrammarParseError(
        span: span,
        expected: "valid expression",
        got: string.drop_start(message, string.length("Parse error: end of input got ")),
        context: "",
      )
      let diagnostic = error_reporter.parse_error_to_diagnostic(grammar_error, source, path)
      io.println(error_reporter.format_diagnostic(diagnostic, source))
    }
    CompilerImportError(message, _span) -> {
      io.println("Import error: " <> message)
    }
    CompilerCircularImport(cycle, _span) -> {
      io.println("Circular import detected: " <> string.join(cycle, " -> "))
    }
    CompilerModuleNotFound(path, _span) -> {
      io.println("Module not found: " <> path)
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

/// Convert parsed expressions to statements.
fn exprs_to_stmts(exprs: List(TaoExpr)) -> List(tao_ast.Stmt) {
  list.flat_map(exprs, fn(expr) {
    case expr {
      TaoLet(name, mutable, _type_annotation, value, span) -> {
        // Convert let expression to StmtLet
        // Note: Type annotations are not yet parsed, so we ignore them for now
        let ast_value = expr_to_ast(value)
        [tao_ast.StmtLet(name, mutable, None, ast_value, span)]
      }
      TaoSimpleFn(name, params, return_type, body, span) -> {
        // Function definitions become StmtFn
        let ast_params = params_to_ast_params(params, span)
        let ast_body = expr_to_ast(body)
        let ast_return_type = case return_type {
          Some(t) -> Some(tao_ast.TVar(t))
          None -> None
        }
        [tao_ast.StmtFn(name, [], ast_params, ast_return_type, ast_body, span)]
      }
      TaoBlockExpr(stmts, _span) -> {
        // Blocks contain statements - convert each statement
        list.flat_map(stmts, fn(stmt_expr) {
          case stmt_expr {
            TaoLet(name, mutable, _type_annotation, value, span) -> {
              let ast_value = expr_to_ast(value)
              [tao_ast.StmtLet(name, mutable, None, ast_value, span)]
            }
            TaoSimpleFn(name, params, return_type, body, span) -> {
              // Function definitions become StmtFn
              let ast_params = params_to_ast_params(params, span)
              let ast_body = expr_to_ast(body)
              let ast_return_type = case return_type {
                Some(t) -> Some(tao_ast.TVar(t))
                None -> None
              }
              [tao_ast.StmtFn(name, [], ast_params, ast_return_type, ast_body, span)]
            }
            _ -> {
              let ast_expr = expr_to_ast(stmt_expr)
              [tao_ast.StmtExpr(ast_expr, get_expr_span(stmt_expr))]
            }
          }
        })
      }
      TaoIf(_, _, _, _) -> {
        // If expressions become StmtExpr
        let ast_expr = expr_to_ast(expr)
        [tao_ast.StmtExpr(ast_expr, get_expr_span(expr))]
      }
      _ -> {
        // Other expressions become StmtExpr
        let ast_expr = expr_to_ast(expr)
        [tao_ast.StmtExpr(ast_expr, get_expr_span(expr))]
      }
    }
  })
}

fn params_to_ast_params(params: List(#(String, option.Option(String))), span: Span) -> List(tao_ast.Param) {
  list.map(params, fn(param) {
    let #(name, type_opt) = param
    let type_ann = case type_opt {
      Some(t) -> Some(tao_ast.TVar(t))
      None -> None
    }
    tao_ast.Param(name, type_ann, span)
  })
}


fn debug_term(term: ast.Term) -> String {
  // Simple debug representation
  // In a full implementation, this would pretty-print the AST
  core_syntax.format(term)
}

fn file_type_to_string(file_type: FileType) -> String {
  case file_type {
    Core -> "Core language (.core.tao)"
    Tao -> "Tao high-level language (.tao)"
  }
}
