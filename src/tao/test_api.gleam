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
import syntax/grammar.{type ParseResult, ParseError, type ParseError as GrammarParseError, type Span, Span, type Span as GrammarSpan}
import syntax/error_reporter.{type_error_to_diagnostic, parse_error_to_diagnostic}
import syntax/source_snippet.{format_diagnostic}
import tao/desugar.{desugar_module, type DesugarContext}
import tao/global_context.{type GlobalContext, new_context, with_prelude, set_current_module}
import core/ast.{type Value}
import core/state.{type State, State, type Error as CoreError, initial_state, initial_ffis, SyntaxError, NameShadow, TypeMismatch}
import core/infer.{infer}
import core/eval.{eval}
import core/quote.{quote, normalize}
import core/subst.{force}
import core/syntax as core_syntax
import core/unify as unify
import gleam/list
import gleam/int
import gleam/option.{type Option, Some, None}
import gleam/string
import tao/ast as t
import tao/import_ast.{type Import, ImportModule, ImportAlias, ImportSelective, ImportSelectiveAlias, ImportWildcard, ImportName, ImportType, ImportOperator}

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

      // Check for duplicate top-level definitions
      case check_duplicate_names(body, file_path) {
        Error(dup_errs) -> #(dup_errs, [])
        Ok(_) -> {
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
                // Pass code_only for error formatting (AST spans are from stripped source)
                run_test(test_item, body, ctx, file_path, code_only)
              })

              #([], results)
            }
          }
        }
      }
    }
  }
}

/// Check for duplicate top-level definitions in a module body.
/// Shadowing is not allowed at the global level.
fn check_duplicate_names(
  body: List(t.Stmt),
  file_path: String,
) -> Result(Nil, List(CoreError)) {
  let names_and_spans = list.flat_map(body, fn(stmt) {
    case stmt {
      t.StmtLet(name, _, _, _, span) -> [#(name, span)]
      t.StmtFn(name, _, _, _, _, span) -> [#(name, span)]
      t.StmtType(name, _, _, span) -> [#(name, span)]
      _ -> []
    }
  })
  // Find duplicates
  let duplicates = find_duplicates(names_and_spans, [], [])
  case duplicates {
    [] -> Ok(Nil)
    [#(name, first_span, second_span), ..] -> {
      let err = NameShadow(name, first_span, second_span)
      Error([err])
    }
  }
}

/// Find duplicate names, returning list of #(name, first_span, second_span).
fn find_duplicates(
  names: List(#(String, grammar.Span)),
  seen: List(#(String, grammar.Span)),
  acc: List(#(String, grammar.Span, grammar.Span)),
) -> List(#(String, grammar.Span, grammar.Span)) {
  case names {
    [] -> acc
    [#(name, span), ..rest] -> {
      // Check if name is already in seen
      case find_in_list(seen, name) {
        Some(first_span) ->
          find_duplicates(rest, seen, [#(name, first_span, span), ..acc])
        None ->
          find_duplicates(rest, [#(name, span), ..seen], acc)
      }
    }
  }
}

/// Find a name in a list of #(name, span), returning the span if found.
fn find_in_list(
  list: List(#(String, grammar.Span)),
  name: String,
) -> Option(grammar.Span) {
  case list {
    [] -> None
    [#(n, s), ..rest] -> {
      case n == name {
        True -> Some(s)
        False -> find_in_list(rest, name)
      }
    }
  }
}

/// Extract all defined names from a module body (for validating test expected values).
pub fn get_defined_names(body: List(t.Stmt)) -> List(String) {
  list.flat_map(body, fn(stmt) {
    case stmt {
      t.StmtLet(name, _, _, _, _) -> [name]
      t.StmtFn(name, _, _, _, _, _) -> [name]
      t.StmtType(name, _, constructors, _) -> {
        // Include type name and constructor names
        let ctr_names = list.flat_map(constructors, fn(ctr) {
          case ctr {
            t.Constructor(ctr_name, _, _) -> [ctr_name]
          }
        })
        [name, ..ctr_names]
      }
      t.StmtImport(import_item, _) -> {
        // Extract imported names from the Import item
        extract_import_names(import_item)
      }
      _ -> []
    }
  })
}

/// Get span from any statement variant.
fn get_stmt_span(stmt: t.Stmt) -> GrammarSpan {
  case stmt {
    t.StmtLet(_, _, _, _, span) -> span
    t.StmtFn(_, _, _, _, _, span) -> span
    t.StmtImport(_, span) -> span
    t.StmtType(_, _, _, span) -> span
    t.StmtFor(_, _, _, span) -> span
    t.StmtWhile(_, _, span) -> span
    t.StmtLoop(_, span) -> span
    t.StmtBreak(span) -> span
    t.StmtContinue(span) -> span
    t.StmtReturn(_, span) -> span
    t.StmtYield(_, span) -> span
    t.StmtExpr(_, span) -> span
    t.StmtBind(_, _, span) -> span
    t.StmtMut(_, _, span) -> span
    t.StmtTest(_, _, span) -> span
    t.StmtRun(_, span) -> span
  }
}

/// Extract names from an import item.
fn extract_import_names(import_item: Import) -> List(String) {
  case import_item {
    ImportModule(_, _) -> []
    ImportAlias(_, _, _) -> []
    ImportSelective(_, items, _) -> {
      list.flat_map(items, fn(item) {
        case item {
          ImportName(name, Some(alias)) -> [alias]
          ImportName(name, None) -> [name]
          ImportType(name, Some(alias)) -> [alias]
          ImportType(name, None) -> [name]
          ImportOperator(name, Some(alias)) -> [alias]
          ImportOperator(name, None) -> [string.replace(name, "+", "add")]
        }
      })
    }
    ImportSelectiveAlias(_, _, items, _) -> {
      list.flat_map(items, fn(item) {
        case item {
          ImportName(name, Some(alias)) -> [alias]
          ImportName(name, None) -> [name]
          ImportType(name, Some(alias)) -> [alias]
          ImportType(name, None) -> [name]
          ImportOperator(name, Some(alias)) -> [alias]
          ImportOperator(name, None) -> [string.replace(name, "+", "add")]
        }
      })
    }
    ImportWildcard(_, _) -> []
  }
}

/// Fix the expected expression's span to match the actual line in the file.
/// The parsed expected expression gets default spans (line 1), but we need
/// it to point to the actual line where it appears in the source.
fn fix_expected_span(expr: Expr, test_span: GrammarSpan, source: String, file: String) -> Expr {
  let fixed = Span(
    file,
    test_span.start_line,
    test_span.start_col,
    test_span.end_line,
    test_span.end_col,
  )
  case expr {
    TaoInt(n, _) -> TaoInt(n, fixed)
    TaoFloat(n, _) -> TaoFloat(n, fixed)
    TaoStr(s_val, _) -> TaoStr(s_val, fixed)
    TaoVar(name, _) -> TaoVar(name, fixed)
    TaoBinOp(left, op, right, _) ->
      TaoBinOp(fix_expected_span(left, test_span, source, file), op, fix_expected_span(right, test_span, source, file), fixed)
    TaoUnaryOp(op, arg, _) ->
      TaoUnaryOp(op, fix_expected_span(arg, test_span, source, file), fixed)
    TaoApp(fn_expr, args, _) ->
      TaoApp(fix_expected_span(fn_expr, test_span, source, file), list.map(args, fn(a) { fix_expected_span(a, test_span, source, file) }), fixed)
    TaoCtr(name, args, _) ->
      TaoCtr(name, list.map(args, fn(a) { fix_expected_span(a, test_span, source, file) }), fixed)
    TaoLet(name, mutable, type_ann, value, _) ->
      TaoLet(name, mutable, type_ann, fix_expected_span(value, test_span, source, file), fixed)
    TaoBlock(stmts, _) ->
      TaoBlock(list.map(stmts, fn(stmt) { fix_expected_span(stmt, test_span, source, file) }), fixed)
    _ -> expr
  }
}

/// Check if an expected value is valid.
/// - `_` is a wildcard that matches anything
/// - Bare variables must be defined in the module
/// - Other expressions are evaluated normally
fn check_expected(
  expected_expr: Expr,
  defined_names: List(String),
  file: String,
  line: Int,
  expression: String,
  expected_str: String,
  source: String,
) -> Result(Nil, String) {
  case expected_expr {
    TaoVar("_", _) -> {
      // Wildcard - matches anything, no further checking needed
      Ok(Nil)
    }
    TaoVar(name, _) -> {
      // Bare variable - must be defined in the module
      case list.contains(defined_names, name) {
        True -> Ok(Nil)
        False -> {
          Error("Expected value '" <> name <> "' is not defined in this module. "
            <> "Use '_' to match any value, or define '" <> name <> "' first.")
        }
      }
    }
    _ -> {
      // Other expressions (literals, function calls, etc.) - evaluate normally
      Ok(Nil)
    }
  }
}

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
  TestExpr(expression: String, expected: String, span: Span, expected_span: Span)
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
                      // Calculate expected value's column position
                      let expected_col = 3 + string.length(expr_part) + 2 // "> " + expr_part + " ~>"
                      let expected_span = Span(file_path, line_num, expected_col, line_num, expected_col + string.length(expected))
                      let test_expr = TestExpr(expression, expected, span, expected_span)
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
                      let expected_span = Span(file_path, expected_line_num, 1, expected_line_num, string.length(expected_line))
                      let test_expr = TestExpr(expression, expected, span, expected_span)
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
  source: String,
) -> TestResult {
  let file = test_expr.span.file
  let line = test_expr.span.start_line
  // Parse the test expression
  let expr_result: ParseResult(Expr) = parse_expr(test_expr.expression)
  case expr_result.errors {
    [_, ..] as errs -> Fail(file, line, test_expr.expression, test_expr.expected, format_parse_errors(errs, source, file))
    [] -> {
      // Create extended module: original body + test expression as the result
      // Use StmtRun instead of StmtExpr — StmtRun returns its expression as the
      // module result, while StmtExpr discards the result.
      let ast_expr = expr_to_ast(expr_result.ast)
      let expr_span = get_expr_span(expr_result.ast)
      let test_stmt = t.StmtRun(ast_expr, expr_span)
      // Only include definitions that appear before the test in the file
      // TODO: Currently disabled due to type issues, using full body
      let visible_body = original_body
      // let visible_body = list.filter(original_body, fn(stmt) {
      //   get_stmt_span(stmt).start_line < line
      // })
      let extended_body = list.append(visible_body, [test_stmt])
      let extended_module = t.Module(file_path, extended_body, expr_span)

      // Desugar and type-check the extended module
      let extended_ctx = new_context() |> with_prelude()
      let #(extended_term, extended_dc) = desugar_module(extended_module, extended_ctx)
      let eval_state = state_with_constructors(extended_dc, initial_state)
      let #(_value, actual_type, type_state) = infer(eval_state, extended_term)

      case type_state.errors {
        [_, ..] as errs -> {
          // Type error in test expression
          Fail(file, line, test_expr.expression, test_expr.expected, format_type_errors(errs, source, file))
        }
        [] -> {
          // Evaluate the extended module - the result is the test expression's value
          let actual_value = eval(initial_ffis, [], extended_term)
          // Apply the type substitution to solve any holes
          let forced_actual = force(initial_ffis, type_state.subst, actual_value)

          // Parse and evaluate expected in the same extended context
          let expected_result: ParseResult(Expr) = parse_expr(test_expr.expected)
          case expected_result.errors {
            [_, ..] as errs -> Fail(file, line, test_expr.expression, test_expr.expected, format_parse_errors(errs, source, file))
            [] -> {
              // Fix the expected expression's span to match the actual line in the file
              let expected_expr = fix_expected_span(expected_result.ast, test_expr.expected_span, source, file)
              // Check expected value validity before evaluation
              let defined_names = get_defined_names(visible_body)
              case check_expected(expected_expr, defined_names, file, line, test_expr.expression, test_expr.expected, source) {
                Error(msg) -> {
                  // Undefined variable or invalid expected value
                  Fail(file, line, test_expr.expression, test_expr.expected, msg)
                }
                Ok(_) -> {
                  // Check if expected is wildcard `_`
                  case expected_expr {
                    TaoVar("_", _) -> {
                      // Wildcard - matches any value
                      Pass(file, line, test_expr.expression)
                    }
                    _ -> {
                      // Regular expected value - evaluate and compare
                      check_expected_value(expected_expr, original_body, file_path, test_expr, source, line, forced_actual, actual_type)
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

/// Check if two types match. Returns errors if they don't.
fn check_types(
  actual_type: Value,
  expected_type: Value,
  expected_span: GrammarSpan,
  actual_span: GrammarSpan,
  file: String,
) -> Result(Nil, List(CoreError)) {
  // Fix spans to use the correct file path
  let fixed_expected = Span(
    file,
    expected_span.start_line,
    expected_span.start_col,
    expected_span.end_line,
    expected_span.end_col,
  )
  let fixed_actual = Span(
    file,
    actual_span.start_line,
    actual_span.start_col,
    actual_span.end_line,
    actual_span.end_col,
  )
  let init_state = State(..initial_state, errors: [])
  let #(_subst, state) = unify.unify(init_state, 0, expected_type, actual_type, fixed_expected, fixed_actual)
  case state.errors {
    [] -> Ok(Nil)
    errs -> Error(errs)
  }
}

/// Evaluate expected value and compare with actual.
fn check_expected_value(
  expected_expr: Expr,
  original_body: List(t.Stmt),
  file_path: String,
  test_expr: TestExpr,
  source: String,
  line: Int,
  forced_actual: Value,
  actual_type: Value,
) -> TestResult {
  let file = test_expr.span.file
  let expected_ast = expr_to_ast(expected_expr)
  let expected_span = get_expr_span(expected_expr)
  let expected_stmt = t.StmtRun(expected_ast, expected_span)
  let expected_body = list.append(original_body, [expected_stmt])
  let expected_module = t.Module(file_path, expected_body, expected_span)

  let expected_ctx = new_context() |> with_prelude()
  let #(expected_term, expected_dc) = desugar_module(expected_module, expected_ctx)
  let expected_eval_state = state_with_constructors(expected_dc, initial_state)
  let #(_evalue, expected_type, expected_type_state) = infer(expected_eval_state, expected_term)

  case expected_type_state.errors {
    [_, ..] as errs -> Fail(file, line, test_expr.expression, test_expr.expected, format_type_errors(errs, source, file))
    [] -> {
      // Check types match before comparing values
      case check_types(actual_type, expected_type, expected_span, test_expr.span, file) {
        Error(type_errs) -> {
          // Type mismatch - report with full diagnostics
          Fail(file, line, test_expr.expression, test_expr.expected, format_type_errors(type_errs, source, file))
        }
        Ok(Nil) -> {
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

/// Format a type value as a string for display.
fn format_type(ty: Value) -> String {
  let span = Span("", 0, 0, 0, 0)
  let term = quote(initial_ffis, 0, ty, span)
  core_syntax.format(term)
}

/// Format grammar parse errors as a readable message with full diagnostics.
/// Shows ALL errors with span, code snippet, and hints.
fn format_parse_errors(errors: List(GrammarParseError), source: String, file: String) -> String {
  case errors {
    [] -> "<parse error>"
    errs -> {
      let diagnostics = list.map(errs, fn(err) {
        // Fix span: grammar parser swaps line/col
        // err.span.start_col is actually the line
        // err.span.end_line is actually the column
        let fixed_span = Span(
          file,
          err.span.start_col,
          err.span.end_line,
          err.span.start_col,
          err.span.end_line + string.length(err.got),
        )
        let grammar_err = ParseError(
          span: fixed_span,
          expected: err.expected,
          got: err.got,
          context: "",
        )
        let diagnostic = parse_error_to_diagnostic(grammar_err, source, file)
        format_diagnostic(diagnostic, source)
      })
      string.join(diagnostics, "\n\n")
    }
  }
}

/// Format core state type errors as a readable message with full diagnostics.
/// Shows ALL errors with span, code snippet, and hints.
fn format_type_errors(errors: List(CoreError), source: String, file: String) -> String {
  case errors {
    [] -> "<type error>"
    errs -> {
      let diagnostics = list.map(errs, fn(err) {
        let diagnostic = type_error_to_diagnostic(err, source, file)
        format_diagnostic(diagnostic, source)
      })
      string.join(diagnostics, "\n\n")
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
        // Convert ConstructorDecl to Constructor with proper field types
        t.StmtType(name, type_params, list.map(constructors, fn(ctr) {
          case ctr {
            TaoCtrDecl(ctr_name, fields, ctr_span) -> {
              let ast_fields = list.map(fields, fn(field_type_str) {
                t.UnnamedField(t.TVar(field_type_str))
              })
              t.Constructor(ctr_name, ast_fields, ctr_span)
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
      TaoImport(import_item, span) -> {
        t.StmtImport(import_item, span)
      }
      TaoLet(name, mutable, type_annotation, value, span) -> {
        // Let bindings should be StmtLet, not StmtExpr
        let ast_value = expr_to_ast(value)
        let ast_type = case type_annotation {
          Some(t) -> Some(t.TVar(t))
          None -> None
        }
        t.StmtLet(name, mutable, ast_type, ast_value, span)
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
