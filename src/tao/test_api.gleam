// ============================================================================
// STANDARD LIBRARY TEST API
// ============================================================================
/// Internal testing API for standard library modules.
///
/// Returns `#(List(Error), List(TestResult))` - no formatting.
/// CLI and Gleam tests use the same API but handle output differently.
///
/// For detailed documentation see:
/// - **[../plans/tao/18-stdlib-testing.md](../plans/tao/18-stdlib-testing.md)** - Testing infrastructure plan
import tao/syntax.{parse_module, type Expr, parse as parse_expr, Int as TaoInt, Float as TaoFloat, Str as TaoStr, Var as TaoVar, BinOp as TaoBinOp, UnaryOp as TaoUnaryOp, OverloadedFn as TaoOverloadedFn, OverloadedApp as TaoOverloadedApp, Let as TaoLet, Block as TaoBlock, SimpleFn as TaoSimpleFn, App as TaoApp, Lambda as TaoLambda, Match as TaoMatch, If as TaoIf, For as TaoFor, While as TaoWhile, Loop as TaoLoop, Break as TaoBreak, Continue as TaoContinue, Test as TaoTest, Run as TaoRun, Import as TaoImport, Ctr as TaoCtr, TypeDecl as TaoTypeDecl, expr_to_ast}
import syntax/grammar.{type ParseResult, type Span, Span}
import tao/desugar.{desugar_module}
import tao/global_context.{type GlobalContext, new_context, with_prelude, set_current_module}
import core/core.{type Term, type State, type Value, type Error as CoreError, initial_state, infer, eval, quote, normalize, Err, TypeMismatch, VarUndefined, CtrUndefined, HoleUnsolved, MatchRedundantCase, MatchMissingCase, RcdMissingFields, DotFieldNotFound, DotOnNonCtr, InfiniteType, SpineMismatch, ArityMismatch, NotAFunction, PatternMismatch, TODO as CoreTODO, ComptimePermissionDenied}
import core/syntax as core_syntax
import gleam/list
import gleam/option.{type Option, Some, None}
import gleam/string
import gleam/int
import tao/ast.{type Stmt, Module, StmtExpr, StmtLet, StmtFn, StmtBind, StmtMut, StmtTest, StmtRun, StmtType, StmtFor, StmtWhile, StmtLoop, StmtBreak, StmtContinue, StmtReturn, StmtYield, StmtImport}
import tao/syntax as tao_syntax

// ============================================================================
// TYPES
// ============================================================================

/// Error during testing.
pub type Error {
  /// Parse error
  ParseError(message: String, span: Span)
  /// Type error
  TypeError(message: String, span: Span)
  /// Exhaustiveness error
  ExhaustivenessError(message: String, span: Span)
  /// Evaluation error
  EvaluationError(message: String, span: Span)
  /// Desugar error
  DesugarError(message: String, span: Span)
}

/// Result of running a single test.
pub type TestResult {
  /// Test passed
  Pass(expression: String)
  /// Test failed - value didn't match expected
  Fail(expression: String, expected: String, actual: String)
}

/// Result of running a test file.
pub type TestFileResult {
  TestFileResult(
    errors: List(Error),
    results: List(TestResult),
  )
}

// ============================================================================
// MAIN API
// ============================================================================

/// Parse, type-check, and evaluate a test file.
///
/// Returns: `#(errors, test_results)`
/// - `errors`: Parse/type/exhaustiveness errors (empty if none)
/// - `test_results`: List of pass/fail for each test expression
///
/// Test file format:
/// ```tao
/// > expression
/// expected_result
/// ```
pub fn run_test_file(source: String, file_path: String) -> #(List(Error), List(TestResult)) {
  // 1. Parse Tao source
  let parse_result = parse_module(source)
  
  case parse_result.errors {
    [err, ..] -> {
      let error = ParseError("Parse error: " <> err.expected <> " got " <> err.got, err.span)
      #([error], [])
    }
    [] -> {
      // 2. Convert expressions to module and desugar
      let body = exprs_to_stmts(parse_result.ast)
      let module = Module(file_path, body, get_module_span(body, file_path))
      let ctx = new_context() |> with_prelude()

      let #(core_term, _desugar_ctx) = desugar_module(module, ctx)

      // 3. Type check
      let state = initial_state
      let #(_value, _type, state) = infer(state, core_term)

      case state.errors {
        [_, ..] as errors -> #(convert_core_errors(errors), [])
        [] -> {
          // 4. Extract and run tests from source
          let tests = extract_repl_tests(source)
          let results = list.map(tests, fn(test_item) {
            run_test(test_item, state)
          })

          #([], results)
        }
      }
    }
  }
}

/// Convert Core errors to test API errors.
fn convert_core_errors(errors: List(CoreError)) -> List(Error) {
  list.map(errors, fn(err) {
    case err {
      TypeMismatch(expected, got, span, _ctx) -> {
        TypeError("Type mismatch: expected " <> format_value(expected) <> " got " <> format_value(got), span)
      }
      VarUndefined(index, span) -> {
        TypeError("Undefined variable (index: " <> int.to_string(index) <> ")", span)
      }
      CtrUndefined(tag, span) -> {
        TypeError("Undefined constructor: " <> tag, span)
      }
      HoleUnsolved(id, span) -> {
        TypeError("Unsolved hole: " <> int.to_string(id), span)
      }
      MatchRedundantCase(span) -> {
        ExhaustivenessError("Redundant pattern case", span)
      }
      MatchMissingCase(span, pattern) -> {
        ExhaustivenessError("Missing pattern case", span)
      }
      RcdMissingFields(names, span) -> {
        TypeError("Missing record fields: " <> string.join(names, ", "), span)
      }
      DotFieldNotFound(name, _value, span) -> {
        TypeError("Field not found: " <> name, span)
      }
      DotOnNonCtr(value, _name, span) -> {
        TypeError("Cannot access field on non-record value", span)
      }
      InfiniteType(hole_id, ty, span1, span2) -> {
        TypeError("Infinite type for hole " <> int.to_string(hole_id), span1)
      }
      SpineMismatch(span1, span2) -> {
        TypeError("Spine mismatch", span1)
      }
      ArityMismatch(span1, span2) -> {
        TypeError("Arity mismatch", span1)
      }
      NotAFunction(fun, fun_ty) -> {
        TypeError("Not a function", Span("", 0, 0, 0, 0))
      }
      PatternMismatch(pattern, expected_ty, pattern_span, value_span) -> {
        TypeError("Pattern mismatch", pattern_span)
      }
      CoreTODO(message) -> {
        TypeError("TODO: " <> message, Span("", 0, 0, 0, 0))
      }
      ComptimePermissionDenied(op, span, required) -> {
        TypeError("Comptime permission denied: " <> op, span)
      }
      core.SyntaxError(span, expected, got, context) -> {
        TypeError("Syntax error: expected " <> expected <> " got " <> got, span)
      }
      core.CtrUnsolvedParam(tag, ctr, id, span) -> {
        TypeError("Constructor unsolved parameter: " <> tag, span)
      }
    }
  })
}

// ============================================================================
// TEST EXTRACTION
// ============================================================================

/// Test expression extracted from source.
type TestExpr {
  TestExpr(expression: String, expected: String, span: Span)
}

/// Extract REPL-style tests from source.
///
/// Format:
/// ```
/// > expression
/// expected
/// ```
fn extract_repl_tests(source: String) -> List(TestExpr) {
  let lines = string.split(source, "\n")
  let indexed_lines = list.index_map(lines, fn(line, index) {
    #(index + 1, line)  // 1-based line numbers
  })
  
  extract_test_pairs(indexed_lines, source, [])
}

/// Extract test pairs from lines.
fn extract_test_pairs(
  lines: List(#(Int, String)),
  source: String,
  acc: List(TestExpr),
) -> List(TestExpr) {
  case lines {
    [] -> list.reverse(acc)
    
    [line, ..rest] -> {
      let #(line_num, line_content) = line
      let trimmed = string.trim(line_content)
      
      // Check for test expression: `> ...`
      case string.starts_with(trimmed, "> ") {
        True -> {
          let expression = string.trim(string.slice(trimmed, 2, string.length(trimmed)))
          
          // Find next non-empty line as expected result
          case find_next_non_empty(rest) {
            Some(#(expected_line_num, expected_line)) -> {
              let expected = string.trim(expected_line)
              let span = Span(source, line_num, 0, expected_line_num, 0)
              let test_expr = TestExpr(expression, expected, span)
              // Skip past the expected line
              let remaining = skip_until_empty_or_test(rest)
              extract_test_pairs(remaining, source, [test_expr, ..acc])
            }
            None -> {
              // No expected result found, skip this test
              extract_test_pairs(rest, source, acc)
            }
          }
        }
        False -> extract_test_pairs(rest, source, acc)
      }
    }
  }
}

/// Find next non-empty line that's not a comment.
fn find_next_non_empty(lines: List(#(Int, String))) -> Option(#(Int, String)) {
  case lines {
    [] -> None
    [line, ..rest] -> {
      let #(_num, content) = line
      let trimmed = string.trim(content)
      case trimmed {
        "" -> find_next_non_empty(rest)
        "// " <> _ -> find_next_non_empty(rest)
        _ -> Some(line)
      }
    }
  }
}

/// Skip lines until empty line or next test.
fn skip_until_empty_or_test(lines: List(#(Int, String))) -> List(#(Int, String)) {
  case lines {
    [] -> []
    [line, ..rest] -> {
      let #(_num, content) = line
      let trimmed = string.trim(content)
      case trimmed {
        "" -> rest
        "> " <> _ -> lines  // Next test starts here
        _ -> skip_until_empty_or_test(rest)
      }
    }
  }
}

// ============================================================================
// TEST EXECUTION
// ============================================================================

/// Run a single test.
fn run_test(test_expr: TestExpr, state: State) -> TestResult {
  // Parse and evaluate expression
  let expr_result: ParseResult(Expr) = parse_expr(test_expr.expression)
  case expr_result.errors {
    [_, ..] -> Fail(test_expr.expression, test_expr.expected, "<parse error>")
    [] -> {
      let expr_term = expr_to_core_term([expr_result.ast], state)
      let actual_value = eval(state.ffi, [], expr_term)

      // Parse and evaluate expected
      let expected_result: ParseResult(Expr) = parse_expr(test_expr.expected)
      case expected_result.errors {
        [_, ..] -> Fail(test_expr.expression, test_expr.expected, "<parse error>")
        [] -> {
          let expected_term = expr_to_core_term([expected_result.ast], state)
          let expected_value = eval(state.ffi, [], expected_term)

          // Compare values
          case values_equal(actual_value, expected_value) {
            True -> Pass(test_expr.expression)
            False -> Fail(test_expr.expression, test_expr.expected, format_value(actual_value))
          }
        }
      }
    }
  }
}

/// Convert Tao AST to Core term.
fn expr_to_core_term(exprs: List(Expr), state: State) -> Term {
  // Build a block expression
  let span = Span("", 0, 0, 0, 0)

  case exprs {
    [] -> Err("No expressions", span)
    [expr, ..] -> {
      // Desugar single expression
      let body = exprs_to_stmts(exprs)
      let module = Module("", body, span)
      let ctx = new_context() |> with_prelude()
      let #(term, _ctx) = desugar_module(module, ctx)
      term
    }
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
  let term = quote(initial_state.ffi, 0, value, span)
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
fn exprs_to_stmts(exprs: List(Expr)) -> List(Stmt) {
  list.map(exprs, fn(expr) {
    StmtExpr(expr_to_ast(expr), get_expr_span(expr))
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
    TaoTypeDecl(_, _, span) -> span
  }
}

/// Get module span from body.
fn get_module_span(body: List(Stmt), path: String) -> Span {
  case body {
    [] -> Span(path, 0, 0, 0, 0)
    [stmt, ..] -> {
      case stmt {
        StmtExpr(_, span) -> span
        StmtLet(_, _, _, _, span) -> span
        StmtFn(_, _, _, _, _, span) -> span
        StmtBind(_, _, span) -> span
        StmtMut(_, _, span) -> span
        StmtTest(_, _, span) -> span
        StmtRun(_, span) -> span
        StmtType(_, _, _, span) -> span
        StmtFor(_, _, _, span) -> span
        StmtWhile(_, _, span) -> span
        StmtLoop(_, span) -> span
        StmtBreak(span) -> span
        StmtContinue(span) -> span
        StmtReturn(_, span) -> span
        StmtYield(_, span) -> span
        StmtImport(_, span) -> span
      }
    }
  }
}
