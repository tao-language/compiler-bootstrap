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
import tao/syntax.{parse_module, type Expr, parse as parse_expr, Int as TaoInt, Float as TaoFloat, Str as TaoStr, Var as TaoVar, BinOp as TaoBinOp, UnaryOp as TaoUnaryOp, OverloadedFn as TaoOverloadedFn, OverloadedApp as TaoOverloadedApp, Let as TaoLet, Block as TaoBlock, SimpleFn as TaoSimpleFn, App as TaoApp, Lambda as TaoLambda, Match as TaoMatch, If as TaoIf, For as TaoFor, While as TaoWhile, Loop as TaoLoop, Break as TaoBreak, Continue as TaoContinue, Test as TaoTest, Run as TaoRun, Import as TaoImport, Ctr as TaoCtr, TypeDecl as TaoTypeDecl, ConstructorDecl as TaoCtrDecl, expr_to_ast}
import syntax/grammar.{type ParseResult, type Span, Span}
import tao/desugar.{desugar_module, type DesugarContext}
import tao/global_context.{type GlobalContext, new_context, with_prelude, set_current_module}
import core/ast.{type Term, type Value, Err as CoreErr}
import core/state.{type State, type Error as CoreError, initial_state, SyntaxError, TypeMismatch, VarUndefined, CtrUndefined, HoleUnsolved, MatchRedundantCase, MatchMissingCase, RcdMissingFields, DotFieldNotFound, DotOnNonCtr, InfiniteType, SpineMismatch, ArityMismatch, NotAFunction, PatternMismatch, CtrUnsolvedParam, TODO as CoreTODO, ComptimePermissionDenied}
import core/infer.{infer}
import core/eval.{eval}
import core/quote.{quote, normalize}
import core/syntax as core_syntax
import gleam/list
import gleam/option.{type Option, Some, None}
import gleam/string
import tao/ast.{type Stmt, Module, StmtExpr, StmtLet, StmtFn, StmtBind, StmtMut, StmtTest, StmtRun, StmtType, StmtFor, StmtWhile, StmtLoop, StmtBreak, StmtContinue, StmtReturn, StmtYield, StmtImport, Constructor}

// ============================================================================
// TYPES
// ============================================================================

/// Result of running a single test.
pub type TestResult {
  /// Test passed
  Pass(expression: String)
  /// Test failed - value didn't match expected
  Fail(expression: String, expected: String, actual: String)
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
      let module = Module(file_path, body, get_module_span(body, file_path))
      let ctx = new_context() |> with_prelude()

      let #(core_term, desugar_ctx) = desugar_module(module, ctx)

      // 3. Initialize state with constructor environment from desugaring
      let state = state_with_constructors(desugar_ctx, initial_state)
      let #(_value, _type, state) = infer(state, core_term)

      case state.errors {
        [_, ..] as errors -> #(errors, [])
        [] -> {
          // 4. Extract and run tests from ORIGINAL source (with test lines)
          let tests = extract_repl_tests(source, file_path)
          let results = list.map(tests, fn(test_item) {
            run_test(test_item, state)
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

/// Run a single test.
fn run_test(test_expr: TestExpr, state: State) -> TestResult {
  // Parse and evaluate expression
  let expr_result: ParseResult(Expr) = parse_expr(test_expr.expression)
  case expr_result.errors {
    [_, ..] -> Fail(test_expr.expression, test_expr.expected, "<parse error>")
    [] -> {
      let expr_term = expr_to_core_term([expr_result.ast])
      let actual_value = eval(state.ffi, [], expr_term)

      // Parse and evaluate expected
      let expected_result: ParseResult(Expr) = parse_expr(test_expr.expected)
      case expected_result.errors {
        [_, ..] -> Fail(test_expr.expression, test_expr.expected, "<parse error>")
        [] -> {
          let expected_term = expr_to_core_term([expected_result.ast])
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
fn expr_to_core_term(exprs: List(Expr)) -> Term {
  // Build a block expression
  let span = Span("", 0, 0, 0, 0)

  case exprs {
    [] -> CoreErr("No expressions", span)
    [_expr, ..] -> {
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
    case expr {
      TaoTypeDecl(name, constructors, span) -> {
        // Type declarations should be StmtType, not StmtExpr
        // Convert ConstructorDecl to Constructor
        StmtType(name, [], list.map(constructors, fn(ctr) {
          case ctr {
            TaoCtrDecl(ctr_name, _fields, ctr_span) -> {
              // For nullary constructors (True, False), ignore fields
              // This is a simplification - proper type handling would require parsing field types
              Constructor(ctr_name, [], ctr_span)
            }
          }
        }), span)
      }
      _ -> StmtExpr(expr_to_ast(expr), get_expr_span(expr))
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

// ============================================================================
// STATE INITIALIZATION WITH CONSTRUCTORS (Phase 2)
// ============================================================================

/// Initialize Core State with constructor environment from desugaring.
/// Merges DesugarContext.ctrs into State.ctrs for type checking.
fn state_with_constructors(dc: DesugarContext, initial: core.State) -> core.State {
  // Merge DesugarContext.ctrs into State.ctrs
  // Both are CtrEnv (List(#(String, CtrDef)))
  // Prepend desugar context constructors so they take precedence
  let merged_ctrs = list.append(dc.ctrs, initial.ctrs)
  core.State(..initial, ctrs: merged_ctrs)
}
