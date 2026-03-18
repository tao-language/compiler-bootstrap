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
import core/core.{type Term, type Error as TypeError, type State, initial_state, infer, eval, quote, Err, force}
import core/syntax as core_syntax
import tao/syntax.{parse as tao_parse, get_expr_span, type Expr as TaoExpr, Var as TaoVar, Int as TaoInt, Float as TaoFloat, BinOp as TaoBinOp, UnaryOp as TaoUnaryOp, OverloadedFn as TaoOverloadedFn, OverloadedApp as TaoOverloadedApp, Let as TaoLet, Block as TaoBlock, SimpleFn as TaoSimpleFn, App as TaoApp, Lambda as TaoLambda, Match as TaoMatch, Str as TaoStr, Test as TaoTest, Run as TaoRun, If as TaoIf, For, While, Loop, Break, Continue, expr_to_ast}
import tao/desugar.{desugar_module}
import tao/global_context.{new_context, with_prelude, set_current_module}
import tao/compiler.{compile_files, compile_single_file, type CompileResult, type CompileErrorType, ParseError as CompilerParseError, ImportError as CompilerImportError, CircularImport as CompilerCircularImport, ModuleNotFound as CompilerModuleNotFound}
import tao/ast.{type Stmt as TaoStmt, StmtExpr as TaoStmtExpr, StmtLet as TaoStmtLet, Module as TaoModule}
import syntax/grammar.{ParseError as GrammarParseError, type ParseError as GrammarParseErrorType, type Span, Span}
import tao/test_parser.{parse_tests, type Test}
import tao/test_filter.{filter_tests, file_base_name}
import tao/test_runner.{run_tests, calculate_summary, get_failures, all_passed, type TestResult, Fail, Error as TestError, TimedOut}
import tao/test_reporter.{report_results, report_final_status, list_test_names}
import gleam/int
import gleam/io
import gleam/list
import gleam/string
import gleam/option.{Some, None}
import simplifile
import syntax/error_reporter

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
          run_test_command(paths, match_pattern, list_tests, verbose, debug)
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
  io.println("  test [paths]    Run tests in specified files or directories")
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
  io.println("  gleam run test lib/prelude/")
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

fn run_test_command(
  paths: List(String),
  match_pattern: String,
  list_tests: Bool,
  verbose: Bool,
  _debug: Bool,
) -> Nil {
  // Default to lib/prelude/ if no paths specified
  let test_paths = case paths {
    [] -> ["lib/prelude/"]
    _ -> paths
  }

  // Collect all tests from all paths
  let all_tests = collect_tests_from_paths(test_paths, verbose)

  // Filter tests by pattern
  let filtered_tests = case match_pattern {
    "" -> all_tests
    pattern -> {
      // Filter by pattern (match against test name or filename)
      list.map(all_tests, fn(pair) {
        let #(tests, file) = pair
        #(filter_tests(tests, [pattern], file), file)
      })
    }
  }

  // List tests or run them
  case list_tests {
    True -> list_all_tests(filtered_tests)
    False -> run_and_report_tests(filtered_tests, verbose)
  }
}

/// Collect tests from all paths
fn collect_tests_from_paths(paths: List(String), verbose: Bool) -> List(#(List(Test), String)) {
  list.flat_map(paths, fn(path) {
    collect_tests_from_path(path, verbose)
  })
}

/// Collect tests from a single path (file or directory)
fn collect_tests_from_path(path: String, verbose: Bool) -> List(#(List(Test), String)) {
  // Check if it's a directory or file
  case simplifile.read(from: path) {
    Ok(contents) -> {
      // It's a file
      let parse_result = parse_tests(contents, path)
      case verbose {
        True -> {
          io.println("✓ Found " <> int.to_string(list.length(parse_result.tests)) <> " tests in " <> path)
          Nil
        }
        False -> Nil
      }
      [#(parse_result.tests, path)]
    }
    Error(_) -> {
      // Might be a directory, try to read it
      collect_tests_from_directory(path, verbose)
    }
  }
}

/// Collect tests from a directory
fn collect_tests_from_directory(dir_path: String, verbose: Bool) -> List(#(List(Test), String)) {
  // For now, just return empty list - directory reading needs simplifile.list_dir
  // This is a placeholder for now
  case verbose {
    True -> {
      io.println("⚠ Directory reading not yet implemented: " <> dir_path)
      Nil
    }
    False -> Nil
  }
  []
}

/// List all tests
fn list_all_tests(tests_with_files: List(#(List(Test), String))) -> Nil {
  // Flatten all tests for listing
  let all_tests = list.flat_map(tests_with_files, fn(pair) {
    let #(tests, _) = pair
    tests
  })
  list_test_names(all_tests)
}

/// Run tests and report results
fn run_and_report_tests(tests_with_files: List(#(List(Test), String)), verbose: Bool) -> Nil {
  // Run tests for each file with its source
  let all_results = list.flat_map(tests_with_files, fn(pair) {
    let #(tests, source) = pair
    run_tests(tests, source)
  })

  let summary = calculate_summary(all_results)

  // Report results using enhanced reporter
  io.println("")
  report_results(all_results, summary, verbose, "")

  // Final status
  report_final_status(all_passed(all_results))
}

/// Report a single test failure (legacy - kept for compatibility)
fn report_test_failure(_result: TestResult) -> Nil {
  // This function is now obsolete - use test_reporter instead
  Nil
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

  // Use multi-file compiler (single file mode)
  let #(ctx, module, compile_errors) = compile_single_file(file.path, file.contents, ".")

  case compile_errors {
    [err, ..] -> {
      // Report compile errors
      io.println("")
      report_compile_error(err)
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
      let #(term, _dc) = desugar_module(module, ctx)

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
      let #(_type_result, _type_annotation, final_state) = infer(initial_state, term)

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

  // Handle parse errors
  let parse_errors = parse_result.errors
  
  case parse_errors {
    [_err, ..] -> {
      // Report parse errors
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
  let type_errors = type_state.errors

  // Report type errors
  case type_errors {
    _ -> {
      io.println("")
      type_errors |> list.each(fn(e) {
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

  // Combine all errors
  let has_errors = { parse_errors |> list.is_empty } == False || { type_errors |> list.is_empty } == False

  // Evaluate the term (even with errors, for debugging)
  case verbose {
    True -> io.println("✓ Evaluating...")
    False -> Nil
  }

  let env = []
  let ffi = initial_state.ffi
  let value = eval(ffi, env, parse_result.ast)
  // Force the value with the substitution from type checking to solve any holes
  let forced_value = force(ffi, type_state.sub, value)

  // Quote back to normal form
  let span = Span("", 0, 0, 0, 0)
  let normal_form = quote(ffi, 0, forced_value, span)

  // Format and print the result
  let formatted = core_syntax.format(normal_form)

  // If there were errors, print delimiter before result
  case has_errors {
    True -> {
      io.println("")
      io.println("-----------------------------------------------------------")
      io.println(formatted)
      Error(TypeError(type_errors))
    }
    False -> {
      io.println(formatted)
      Ok(Nil)
    }
  }
}

fn run_tao(file: File, verbose: Bool, debug: Bool) -> Result(Nil, Error) {
  case verbose {
    True -> io.println("✓ Parsing Tao...")
    False -> Nil
  }

  let parse_result = tao_parse(file.contents)

  // Handle parse errors
  let parse_errors = parse_result.errors

  case parse_errors {
    [_err, ..] -> {
      // Report parse errors
      io.println("")
      parse_errors |> list.each(fn(err) {
        let diagnostic = error_reporter.parse_error_to_diagnostic(err, file.contents, file.path)
        io.println(error_reporter.format_diagnostic(diagnostic, file.contents))
      })
    }
    [] -> {
      case debug {
        True -> {
          io.println("Tao AST parsed successfully")
        }
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
  let module = TaoModule(
    path: file.path,
    body: exprs_to_stmts([parse_result.ast]),
    span: get_expr_span(parse_result.ast),
  )

  let ctx = new_context() |> with_prelude() |> set_current_module(file.path)
  let #(term, _dc) = desugar_module(module, ctx)

  case debug {
    True -> {
      io.println("Core term:")
      io.println(debug_term(term))
    }
    False -> Nil
  }

  // Run type checker
  case verbose {
    True -> io.println("✓ Type checking...")
    False -> Nil
  }

  let #(_type_result, _type_annotation, type_state) = infer(initial_state, term)
  let type_errors = type_state.errors

  // Report type errors
  case type_errors {
    _ -> {
      io.println("")
      type_errors |> list.each(fn(e) {
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

  // Combine all errors
  let has_errors = { parse_errors |> list.is_empty } == False || { type_errors |> list.is_empty } == False

  // Evaluate the term (even with errors, for debugging)
  case verbose {
    True -> io.println("✓ Evaluating...")
    False -> Nil
  }

  let env = []
  let ffi = initial_state.ffi
  let value = eval(ffi, env, term)
  // Force the value with the substitution from type checking to solve any holes
  let forced_value = force(ffi, type_state.sub, value)

  // Quote back to normal form
  let span = Span("", 0, 0, 0, 0)
  let normal_form = quote(ffi, 0, forced_value, span)

  // Format and print the result
  let formatted = core_syntax.format(normal_form)

  // If there were errors, print delimiter before result
  case has_errors {
    True -> {
      io.println("")
      io.println("-----------------------------------------------------------")
      io.println(formatted)
      Error(TypeError(type_errors))
    }
    False -> {
      io.println(formatted)
      Ok(Nil)
    }
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
fn report_compile_error(error: CompileErrorType) {
  case error {
    CompilerParseError(message, _span) -> {
      io.println("Parse error: " <> message)
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
fn exprs_to_stmts(exprs: List(TaoExpr)) -> List(TaoStmt) {
  list.flat_map(exprs, fn(expr) {
    case expr {
      TaoLet(name, mutable, _type_annotation, value, span) -> {
        // Convert let expression to StmtLet
        // Note: Type annotations are not yet parsed, so we ignore them for now
        let ast_value = expr_to_ast(value)
        [TaoStmtLet(name, mutable, None, ast_value, span)]
      }
      TaoIf(_, _, _, _) -> {
        // If expressions become StmtExpr
        let ast_expr = expr_to_ast(expr)
        [TaoStmtExpr(ast_expr, get_expr_span_from_syntax(expr))]
      }
      _ -> {
        // Other expressions become StmtExpr
        let ast_expr = expr_to_ast(expr)
        [TaoStmtExpr(ast_expr, get_expr_span_from_syntax(expr))]
      }
    }
  })
}

fn get_expr_span_from_syntax(expr: TaoExpr) -> Span {
  case expr {
    TaoVar(_, span) -> span
    TaoInt(_, span) -> span
    TaoFloat(_, span) -> span
    TaoBinOp(_, _, _, span) -> span
    TaoUnaryOp(_, _, span) -> span
    TaoOverloadedFn(_, _, _, _, _, _, span) -> span
    TaoOverloadedApp(_, _, span) -> span
    TaoLet(_, _, _, _, span) -> span
    TaoBlock(_, span) -> span
    TaoSimpleFn(_, _, _, _, span) -> span
    TaoApp(_, _, span) -> span
    TaoLambda(_, _, _, span) -> span
    TaoMatch(_, _, span) -> span
    TaoIf(_, _, _, span) -> span
    For(_, _, _, span) -> span
    While(_, _, span) -> span
    Loop(_, span) -> span
    Break(span) -> span
    Continue(span) -> span
    TaoStr(_, span) -> span
    TaoTest(_, _, span) -> span
    TaoRun(_, span) -> span
  }
}

fn debug_term(term: Term) -> String {
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
