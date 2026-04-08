// ============================================================================
// STANDARD LIBRARY TEST API
// ============================================================================
/// Internal testing API for standard library modules.
///
/// Returns `#(List(core.Error), List(TestResult))` - uses Core errors directly.
/// CLI and Gleam tests use the same API but handle output differently.
///
/// For detailed documentation see:
/// - **[../plans/prelude/README.md](../plans/prelude/README.md)** - Prelude implementation plan
/// - **[../plans/tao/18-stdlib-testing.md](../plans/tao/18-stdlib-testing.md)** - Testing infrastructure
import tao/syntax.{parse_module, type Expr, parse as parse_expr, Int as TaoInt, Float as TaoFloat, Str as TaoStr, Var as TaoVar, BinOp as TaoBinOp, UnaryOp as TaoUnaryOp, OverloadedFn as TaoOverloadedFn, OverloadedApp as TaoOverloadedApp, Let as TaoLet, Block as TaoBlock, SimpleFn as TaoSimpleFn, App as TaoApp, Lambda as TaoLambda, Match as TaoMatch, If as TaoIf, For as TaoFor, While as TaoWhile, Loop as TaoLoop, Break as TaoBreak, Continue as TaoContinue, Test as TaoTest, Run as TaoRun, Import as TaoImport, Ctr as TaoCtr, TypeDecl as TaoTypeDecl, ConstructorDecl as TaoCtrDecl, expr_to_ast, block_to_ast, get_expr_span}
import syntax/grammar.{type ParseResult, type ParseError, type Span, Span}
import tao/desugar.{desugar_module, type DesugarContext}
import tao/global_context.{type GlobalContext, new_context, with_prelude, set_current_module}
import core/ast.{type Value}
import core/state.{type State, State, type Error as CoreError, initial_state, initial_ffis, SyntaxError, TypeMismatch, VarUndefined, CtrUndefined, HoleUnsolved, MatchRedundantCase, MatchMissingCase, RcdMissingFields, DotFieldNotFound, DotOnNonCtr, InfiniteType, SpineMismatch, ArityMismatch, NotAFunction, PatternMismatch, CtrUnsolvedParam, TODO as CoreTODO, ComptimePermissionDenied}
import core/infer.{infer}
import core/eval.{eval}
import core/quote.{quote, normalize}
import core/subst.{force}
import core/syntax as core_syntax
import gleam/list
import gleam/int
import gleam/option.{type Option, Some, None}
import gleam/string
import tao/ast as t

// ============================================================================
// TYPES
// ============================================================================

/// Result of running a single test.
pub type TestResult {
  /// Test passed
  Pass(file: String, line: Int, expression: String)
  /// Test failed - value didn't match expected
  Fail(file: String, line: Int, expression: String, expected: String, actual: String)
}

// ============================================================================
// MAIN API
// ============================================================================

/// Parse, type-check, and evaluate a test file.
///
/// Returns: `#(errors, test_results)`
/// - `errors`: All syntax/type/exhaustiveness errors from Core
/// - `test_results`: List of pass/fail for each test expression
///
/// Test file format:
/// ```tao
/// > expression ~> expected
/// ```
/// or
/// ```tao
/// > expression
/// expected
/// ```
pub fn run_test_file(source: String, file_path: String) -> #(List(CoreError), List(TestResult)) {
  // Strip test lines before parsing (> expr ~> expected or > expr\nexpected)
  let code_only = strip_test_lines(source)

  // 1. Parse Tao source with correct filename
  let parse_result = parse_module(code_only, file_path)

  // Collect ALL parse errors, not just the first one
  case parse_result.errors {
    [_, ..] as errors -> {
      let core_errors = list.map(errors, fn(err) {
        // The grammar parser has Span fields mixed up.
        // err.span.start_line is actually the character start position
        // err.span.start_col is actually the line number
        // err.span.end_line is actually the column
        // err.span.end_col is actually the character end position
        // We need to swap them to get the correct span
        let fixed_span = Span(
          file_path,
          err.span.start_col,  // This is actually the line
          err.span.end_line,   // This is actually the column
          err.span.start_col,  // End line same as start for single token
          err.span.end_line + string.length(err.got)  // End column
        )
        SyntaxError(fixed_span, err.expected, err.got, file_path)
      })
      #(core_errors, [])
    }
    [] -> {
      // 2. Convert expressions to module and desugar
      let body = exprs_to_stmts(parse_result.ast)
      let module = t.Module(file_path, body, get_module_span(body, file_path))
      let ctx = new_context() |> with_prelude()

      let #(core_term, desugar_ctx) = desugar_module(module, ctx)

      // 3. Initialize state with constructor environment from desugaring
      let state = state_with_constructors(desugar_ctx, initial_state)
      let #(_value, _type, state) = infer(state, core_term)

      case state.errors {
        [_, ..] as errors -> #(errors, [])
        [] -> {
          // 4. Extract and run tests from ORIGINAL source (with test lines)
          // Each test expression is evaluated in an extended module that includes
          // the original module's bindings, so functions like `not` are in scope.
          let tests = extract_repl_tests(source, file_path)
          let results = list.map(tests, fn(test_item) {
            run_test(test_item, body, ctx, file_path)
          })

          #([], results)
        }
      }
    }
  }
}

// ============================================================================
// TEST EXTRACTION
// ============================================================================

/// Strip test lines from source for parsing.
/// Removes:
/// - Lines starting with `> ` (test expressions)
/// - Lines that are test expected results (after `> ` lines)
pub fn strip_test_lines(source: String) -> String {
  let lines = string.split(source, "\n")
  let indexed_lines = list.index_map(lines, fn(line, index) {
    #(index, line)
  })
  
  let filtered = strip_test_lines_loop(indexed_lines, [], False)
  string.join(list.reverse(filtered), "\n")
}

/// Loop through lines, skipping test lines.
fn strip_test_lines_loop(
  lines: List(#(Int, String)),
  acc: List(String),
  expecting_result: Bool,
) -> List(String) {
  case lines {
    [] -> acc
    [line, ..rest] -> {
      let #(_num, content) = line
      let trimmed = string.trim(content)
      let is_comment = string.starts_with(trimmed, "//")
      let is_test_expr = string.starts_with(trimmed, "> ")
      let has_arrow = string.contains(trimmed, "~>")
      let is_single_line_test = is_test_expr && has_arrow
      
      // Determine next expecting_result state
      let next_expecting_result = case is_test_expr {
        True -> {
          // For single-line tests, don't expect result line
          // For multi-line tests, expect next non-empty line to be result
          case is_single_line_test {
            True -> False
            False -> True
          }
        }
        False -> expecting_result
      }
      
      case trimmed {
        // Test expression line - skip it
        _ if is_test_expr -> {
          strip_test_lines_loop(rest, acc, next_expecting_result)
        }
        // Expected result line (after test expression) - skip it
        _ if expecting_result && trimmed != "" && !is_comment -> {
          strip_test_lines_loop(rest, acc, False)
        }
        // Keep comment, import, and code lines
        _ -> strip_test_lines_loop(rest, [content, ..acc], False)
      }
    }
  }
}

/// Test expression extracted from source.
type TestExpr {
  TestExpr(expression: String, expected: String, span: Span)
}

/// Extract REPL-style tests from source.
///
/// Supports two formats:
/// 1. Single-line: `> expression ~> expected`
/// 2. Multi-line:
///    ```
///    > expression
///    expected
///    ```
fn extract_repl_tests(source: String, file_path: String) -> List(TestExpr) {
  let lines = string.split(source, "\n")
  let indexed_lines = list.index_map(lines, fn(line, index) {
    #(index + 1, line)  // 1-based line numbers
  })
  
  extract_test_pairs(indexed_lines, source, file_path, [])
}

/// Extract test pairs from lines.
fn extract_test_pairs(
  lines: List(#(Int, String)),
  source: String,
  file_path: String,
  acc: List(TestExpr),
) -> List(TestExpr) {
  case lines {
    [] -> list.reverse(acc)
    
    [line, ..rest] -> {
      let #(line_num, line_content) = line
      let trimmed = string.trim(line_content)
      
      // Skip empty lines and comments
      case trimmed {
        "" -> extract_test_pairs(rest, source, file_path, acc)
        "// " <> _ -> extract_test_pairs(rest, source, file_path, acc)
        "/// " <> _ -> extract_test_pairs(rest, source, file_path, acc)
        
        // Skip import lines
        "import " <> _ -> extract_test_pairs(rest, source, file_path, acc)
        
        // Check for test expression: `> ...`
        _ -> {
          case string.starts_with(trimmed, "> ") {
            True -> {
              let rest_content = string.slice(trimmed, 2, string.length(trimmed))
              
              // Check for single-line test with `~>`
              case string.contains(rest_content, "~>") {
                True -> {
                  // Single-line test: `> expr ~> expected`
                  case string.split(rest_content, "~>") {
                    [expr_part, expected_part] -> {
                      let expression = string.trim(expr_part)
                      let expected = string.trim(expected_part)
                      let span = Span(file_path, line_num, 1, line_num, string.length(line_content))
                      let test_expr = TestExpr(expression, expected, span)
                      extract_test_pairs(rest, source, file_path, [test_expr, ..acc])
                    }
                    _ -> extract_test_pairs(rest, source, file_path, acc)
                  }
                }
                False -> {
                  // Multi-line test: `> expr` followed by `expected` on next line
                  let expression = string.trim(rest_content)
                  
                  // Find next non-empty, non-comment line as expected result
                  case find_next_test_line(rest) {
                    Some(#(expected_line_num, expected_line)) -> {
                      let expected = string.trim(expected_line)
                      let span = Span(file_path, line_num, 1, expected_line_num, string.length(expected_line))
                      let test_expr = TestExpr(expression, expected, span)
                      // Skip past the expected line
                      let remaining = skip_past_line(rest, expected_line_num)
                      extract_test_pairs(remaining, source, file_path, [test_expr, ..acc])
                    }
                    None -> extract_test_pairs(rest, source, file_path, acc)
                  }
                }
              }
            }
            False -> extract_test_pairs(rest, source, file_path, acc)
          }
        }
      }
    }
  }
}

/// Find next line that's a test result (not empty, not comment, not starting with >).
fn find_next_test_line(lines: List(#(Int, String))) -> Option(#(Int, String)) {
  case lines {
    [] -> None
    [line, ..rest] -> {
      let #(_num, content) = line
      let trimmed = string.trim(content)
      case trimmed {
        "" -> find_next_test_line(rest)
        "// " <> _ -> find_next_test_line(rest)
        "/// " <> _ -> find_next_test_line(rest)
        "import " <> _ -> find_next_test_line(rest)
        "> " <> _ -> None  // Next test starts, no expected found
        _ -> Some(line)
      }
    }
  }
}

/// Skip lines until we pass the given line number.
fn skip_past_line(lines: List(#(Int, String)), target_line: Int) -> List(#(Int, String)) {
  case lines {
    [] -> []
    [line, ..rest] -> {
      let #(num, _) = line
      case num >= target_line {
        True -> rest  // Skip this line and return rest
        False -> skip_past_line(rest, target_line)
      }
    }
  }
}

// ============================================================================
// TEST EXECUTION
// ============================================================================

/// Run a single test by creating an extended module that includes the test
/// expression. This ensures the test expression has access to the original
/// module's function bindings (like `not`, `and`, `or`, etc.).
fn run_test(
  test_expr: TestExpr,
  original_body: List(t.Stmt),
  ctx: GlobalContext,
  file_path: String,
) -> TestResult {
  let file = test_expr.span.file
  let line = test_expr.span.start_line
  // Parse the test expression
  let expr_result: ParseResult(Expr) = parse_expr(test_expr.expression)
  case expr_result.errors {
    [_, ..] as errs -> Fail(file, line, test_expr.expression, test_expr.expected, format_parse_errors(errs))
    [] -> {
      // Create extended module: original body + test expression as the result
      // Use StmtRun instead of StmtExpr — StmtRun returns its expression as the
      // module result, while StmtExpr discards the result.
      let ast_expr = expr_to_ast(expr_result.ast)
      let expr_span = get_expr_span(expr_result.ast)
      let test_stmt = t.StmtRun(ast_expr, expr_span)
      let extended_body = list.append(original_body, [test_stmt])
      let extended_module = t.Module(file_path, extended_body, expr_span)

      // Desugar and type-check the extended module
      let extended_ctx = new_context() |> with_prelude()
      let #(extended_term, extended_dc) = desugar_module(extended_module, extended_ctx)
      let eval_state = state_with_constructors(extended_dc, initial_state)
      let #(_value, actual_type, type_state) = infer(eval_state, extended_term)

      case type_state.errors {
        [_, ..] as errs -> {
          // Type error in test expression
          Fail(file, line, test_expr.expression, test_expr.expected, format_type_errors(errs))
        }
        [] -> {
          // Evaluate the extended module - the result is the test expression's value
          let actual_value = eval(initial_ffis, [], extended_term)
          // Apply the type substitution to solve any holes
          let forced_actual = force(initial_ffis, type_state.subst, actual_value)

          // Parse and evaluate expected in the same extended context
          let expected_result: ParseResult(Expr) = parse_expr(test_expr.expected)
          case expected_result.errors {
            [_, ..] as errs -> Fail(file, line, test_expr.expression, test_expr.expected, format_parse_errors(errs))
            [] -> {
              // Create extended module for expected expression
              let expected_ast = expr_to_ast(expected_result.ast)
              let expected_span = get_expr_span(expected_result.ast)
              let expected_stmt = t.StmtRun(expected_ast, expected_span)
              let expected_body = list.append(original_body, [expected_stmt])
              let expected_module = t.Module(file_path, expected_body, expected_span)

              let expected_ctx = new_context() |> with_prelude()
              let #(expected_term, expected_dc) = desugar_module(expected_module, expected_ctx)
              let expected_eval_state = state_with_constructors(expected_dc, initial_state)
              let #(_evalue, expected_type, expected_type_state) = infer(expected_eval_state, expected_term)

              case expected_type_state.errors {
                [_, ..] as errs -> Fail(file, line, test_expr.expression, test_expr.expected, format_type_errors(errs))
                [] -> {
                  // Check types match before comparing values
                  case types_match(actual_type, expected_type) {
                    False -> {
                      // Type mismatch - report as type error
                      Fail(file, line, test_expr.expression, test_expr.expected,
                        "Type mismatch: expected " <> format_type(expected_type) <>
                        ", got " <> format_type(actual_type))
                    }
                    True -> {
                      let expected_value = eval(initial_ffis, [], expected_term)
                      let forced_expected = force(initial_ffis, expected_type_state.subst, expected_value)

                      // Compare values
                      case values_equal(forced_actual, forced_expected) {
                        True -> Pass(file, line, test_expr.expression)
                        False -> Fail(file, line, test_expr.expression, test_expr.expected, format_value(forced_actual))
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

/// Check if two types match by comparing their string representation.
fn types_match(t1: Value, t2: Value) -> Bool {
  format_type(t1) == format_type(t2)
}

/// Format a type value as a string for display.
fn format_type(ty: Value) -> String {
  let span = Span("", 0, 0, 0, 0)
  let term = quote(initial_ffis, 0, ty, span)
  core_syntax.format(term)
}

/// Format grammar parse errors as a readable message.
fn format_parse_errors(errors: List(ParseError)) -> String {
  case errors {
    [] -> "<parse error>"
    [first, ..] -> "Parse error: expected " <> first.expected <> ", got " <> first.got
  }
}

/// Format core state type errors as a readable message.
fn format_type_errors(errors: List(CoreError)) -> String {
  case errors {
    [] -> "<type error>"
    [first, ..] -> format_core_error(first)
  }
}

/// Format a single core error for display.
fn format_core_error(error: CoreError) -> String {
  case error {
    SyntaxError(_, expected, got, _) ->
      "Syntax error: expected " <> expected <> ", got " <> got
    TypeMismatch(_, _, _, _) ->
      "Type error: type mismatch"
    CtrUndefined(name, _) ->
      "Constructor error: undefined constructor '" <> name <> "'"
    VarUndefined(index, _) ->
      "Variable error: undefined variable at index " <> int.to_string(index)
    MatchMissingCase(_, _) ->
      "Exhaustiveness error: missing case in pattern match"
    MatchRedundantCase(_) ->
      "Warning: redundant case in pattern match"
    InfiniteType(id, _, _, _) ->
      "Infinite type error: unsolved hole #" <> int.to_string(id)
    HoleUnsolved(id, _) ->
      "Unsolved hole #" <> int.to_string(id)
    _ ->
      "Error: see above for details"
  }
}

/// Check if two values are equal.
fn values_equal(v1: Value, v2: Value) -> Bool {
  // Simple structural comparison via string representation
  value_to_string(v1) == value_to_string(v2)
}

/// Convert value to string for comparison.
fn value_to_string(value: Value) -> String {
  let span = Span("", 0, 0, 0, 0)
  let term = quote([], 0, value, span)
  core_syntax.format(term)
}

/// Format value for display in Fail results.
fn format_value(value: Value) -> String {
  value_to_string(value)
}

// ============================================================================
// HELPERS
// ============================================================================

/// Convert expressions to statements.
pub fn exprs_to_stmts(exprs: List(Expr)) -> List(t.Stmt) {
  list.map(exprs, fn(expr) {
    case expr {
      TaoTypeDecl(name, type_params, constructors, span) -> {
        // Type declarations should be StmtType, not StmtExpr
        // Convert ConstructorDecl to Constructor
        t.StmtType(name, type_params, list.map(constructors, fn(ctr) {
          case ctr {
            TaoCtrDecl(ctr_name, _fields, ctr_span) -> {
              // For nullary constructors (True, False), ignore fields
              // This is a simplification - proper type handling would require parsing field types
              t.Constructor(ctr_name, [], ctr_span)
            }
          }
        }), span)
      }
      TaoSimpleFn(name, params, return_type, body, span) -> {
        // Function definitions should be StmtFn, not StmtExpr
        // This preserves return type annotations for type inference
        let ast_params = list.map(params, fn(param) {
          let #(pname, ptype) = param
          let ast_type = case ptype {
            Some(t) -> Some(t.TVar(t))
            None -> None
          }
          t.Param(pname, ast_type, span)
        })
        let ast_body = block_to_ast(body)
        let ast_return_type = case return_type {
          Some(t) -> Some(t.TVar(t))
          None -> None
        }
        t.StmtFn(name, [], ast_params, ast_return_type, ast_body, span)
      }
      _ -> t.StmtExpr(expr_to_ast(expr), get_expr_span(expr))
    }
  })
}

/// Get span from expression.
fn get_expr_span(expr: Expr) -> Span {
  case expr {
    TaoInt(_, span) -> span
    TaoFloat(_, span) -> span
    TaoStr(_, span) -> span
    TaoVar(_, span) -> span
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
    TaoFor(_, _, _, span) -> span
    TaoWhile(_, _, span) -> span
    TaoLoop(_, span) -> span
    TaoBreak(span) -> span
    TaoContinue(span) -> span
    TaoTest(_, _, span) -> span
    TaoRun(_, span) -> span
    TaoImport(_, span) -> span
    TaoCtr(_, _, span) -> span
    TaoTypeDecl(_, _, _, span) -> span
  }
}

/// Get module span from body.
fn get_module_span(body: List(t.Stmt), path: String) -> Span {
  case body {
    [] -> Span(path, 0, 0, 0, 0)
    [stmt, ..] -> {
      case stmt {
        t.StmtExpr(_, span) -> span
        t.StmtLet(_, _, _, _, span) -> span
        t.StmtFn(_, _, _, _, _, span) -> span
        t.StmtBind(_, _, span) -> span
        t.StmtMut(_, _, span) -> span
        t.StmtTest(_, _, span) -> span
        t.StmtRun(_, span) -> span
        t.StmtType(_, _, _, span) -> span
        t.StmtFor(_, _, _, span) -> span
        t.StmtWhile(_, _, span) -> span
        t.StmtLoop(_, span) -> span
        t.StmtBreak(span) -> span
        t.StmtContinue(span) -> span
        t.StmtReturn(_, span) -> span
        t.StmtYield(_, span) -> span
        t.StmtImport(_, span) -> span
      }
    }
  }
}

// ============================================================================
// STATE INITIALIZATION WITH CONSTRUCTORS (Phase 2)
// ============================================================================

/// Initialize Core State with constructor environment from desugaring.
/// Merges DesugarContext.ctrs into State.ctrs for type checking.
fn state_with_constructors(dc: DesugarContext, initial: State) -> State {
  // Merge DesugarContext.ctrs into State.ctrs
  // Both are CtrEnv (List(#(String, CtrDef)))
  // Prepend desugar context constructors so they take precedence
  let merged_ctrs = list.append(dc.ctrs, initial.ctrs)
  State(..initial, ctrs: merged_ctrs)
}

// ============================================================================
// SUMMARY (Phase 2)
// ============================================================================

/// Summary of test run.
pub type TestSummary {
  TestSummary(
    total: Int,
    passed: Int,
    failed: Int,
  )
}

/// Calculate test run summary.
pub fn calculate_summary(results: List(TestResult)) -> TestSummary {
  list.fold(results, TestSummary(0, 0, 0), fn(acc, result) {
    case result {
      Pass(_, _, _) -> TestSummary(acc.total + 1, acc.passed + 1, acc.failed)
      Fail(_, _, _, _, _) -> TestSummary(acc.total + 1, acc.passed, acc.failed + 1)
    }
  })
}

/// Check if all tests passed.
pub fn all_passed(results: List(TestResult)) -> Bool {
  case results {
    [] -> True
    [result, ..rest] -> {
      case result {
        Pass(_, _, _) -> all_passed(rest)
        Fail(_, _, _, _, _) -> False
      }
    }
  }
}

/// Get failed tests.
pub fn get_failures(results: List(TestResult)) -> List(TestResult) {
  list.filter(results, fn(result) {
    case result {
      Pass(_, _, _) -> False
      Fail(_, _, _, _, _) -> True
    }
  })
}
