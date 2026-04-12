// ============================================================================
// TAO TEST PARSER
// ============================================================================
/// Parser for Tao example-based tests.
///
/// Test syntax:
/// ```tao
/// -- Test name (optional, defaults to expression)
/// > expression
/// expected_result
///
/// -- Single-line format
/// > expression ~> expected
/// ```
///
/// For detailed documentation see:
/// - **[../plans/tao/11-test-system.md](../plans/tao/11-test-system.md)** - Test system specification
import tao/syntax.{type Expr, parse as parse_expr, type MatchClause, MatchClause, Int as EInt, Float as EFloat, Str as EStr, Var as EVar, Let as ELet, Block as EBlock, SimpleFn as ESimpleFn, App as EApp, Lambda as ELambda, BinOp as EBinOp, UnaryOp as EUnaryOp, Match as EMatch, If as EIf, For as EFor, While as EWhile, Loop as ELoop, Break as EBreak, Continue as EContinue, Test as ETest, Run as ERun, Import as EImport, Ctr as ECtr, TypeDecl as ETypeDecl, OverloadedFn as EOverloadedFn, OverloadedApp as EOverloadedApp}
import syntax/grammar.{type ParseResult, ParseResult, type Span, Span}
import gleam/string
import gleam/list
import gleam/int
import gleam/option.{type Option, Some, None}
import gleam/result

// ============================================================================
// TEST AST
// ============================================================================

/// A single test case.
pub type Test {
  Test(
    name: String,
    expression: Expr,
    expected: ExpectedResult,
    span: Span,
    annotations: List(Annotation),
  )
}

/// Expected result can be a pattern or a value.
pub type ExpectedResult {
  /// Pattern match: `Some(_)`, `{a: _}`, etc.
  Pattern(pattern: String)
  /// Raw expression (will be parsed and compared)
  Expression(Expr)
}

/// Test annotations for controlling test behavior.
pub type Annotation {
  /// Skip this test: `-- @skip` or `-- @skip "reason"`
  Skip(reason: String)
  /// Custom timeout in milliseconds: `-- @timeout 5000`
  Timeout(ms: Int)
  /// Group name for filtering: `-- @group parser`
  Group(name: String)
  /// IO test marker: `-- @io`
  IO
  /// Retry count for flaky tests: `-- @retry 3`
  Retry(count: Int)
  /// Test dependency: `-- @requires other_test`
  Requires(test_name: String)
}

/// Result of parsing a file's tests.
pub type ParseTestsResult {
  ParseTestsResult(
    tests: List(Test),
    syntax_errors: List(SyntaxError),
  )
}

/// Syntax error found during parsing.
pub type SyntaxError {
  SyntaxError(
    message: String,
    span: Span,
  )
}

// ============================================================================
// MAIN PARSING FUNCTIONS
// ============================================================================

/// Parse all tests from a Tao source file.
///
/// Returns both tests and any syntax errors found.
pub fn parse_tests(source: String, file: String) -> ParseTestsResult {
  let lines = string.split(source, "\n")
  let indexed_lines = list.index_map(lines, fn(line, index) {
    #(index + 1, line)  // 1-based line numbers
  })
  
  let #(tests, errors, _) = parse_test_blocks(indexed_lines, file, [], [], None)
  
  ParseTestsResult(
    tests: list.reverse(tests),
    syntax_errors: list.reverse(errors),
  )
}

/// Parse test blocks from lines.
///
/// Returns: #(tests, errors, last_annotation)
fn parse_test_blocks(
  lines: List(#(Int, String)),
  file: String,
  acc_tests: List(Test),
  acc_errors: List(SyntaxError),
  pending_annotation: Option(List(Annotation)),
) -> #(List(Test), List(SyntaxError), Option(List(Annotation))) {
  case lines {
    [] -> #(acc_tests, acc_errors, pending_annotation)
    
    [line, ..rest] -> {
      let #(line_num, line_content) = line
      let trimmed = string.trim(line_content)
      
      // Check for annotation comment: `-- @name` or `-- @name value`
      case parse_annotation_line(trimmed, line_num, file) {
        Some(annotations) -> {
          // Accumulate annotations for next test
          let merged = merge_annotations(pending_annotation, annotations)
          parse_test_blocks(rest, file, acc_tests, acc_errors, Some(merged))
        }
        
        None -> {
          // Check for test name comment: `-- Test name`
          case parse_test_name_line(trimmed, line_num, file) {
            Some(name) -> {
              // This is a test name, next lines should be the test
              parse_test_body(
                rest,
                file,
                name,
                option.unwrap(pending_annotation, []),
                acc_tests,
                acc_errors,
              )
            }
            
            None -> {
              // Check for test expression: `> ...`
              case trimmed {
                "> " <> rest_content -> {
                  // Check if it's a single-line test with `~>`
                  case string.contains(rest_content, "~>") {
                    True -> {
                      // Single-line test: `> expr ~> expected`
                      case parse_single_line_test(trimmed, line_num, file, option.unwrap(pending_annotation, [])) {
                        Ok(parsed_test) -> {
                          parse_test_blocks(
                            rest,
                            file,
                            [parsed_test, ..acc_tests],
                            acc_errors,
                            None,
                          )
                        }
                        Error(error) -> {
                          parse_test_blocks(
                            rest,
                            file,
                            acc_tests,
                            [error, ..acc_errors],
                            None,
                          )
                        }
                      }
                    }
                    False -> {
                      // Multi-line test: `> expr\nexpected` (no `~>`)
                      case parse_multi_line_test(rest, file, line_num, rest_content, option.unwrap(pending_annotation, [])) {
                        #(Some(parsed_test), remaining) -> {
                          parse_test_blocks(remaining, file, [parsed_test, ..acc_tests], acc_errors, None)
                        }
                        #(None, remaining) -> {
                          // No expected result found, skip this `> ` line
                          parse_test_blocks(remaining, file, acc_tests, acc_errors, pending_annotation)
                        }
                      }
                    }
                  }
                }
                ">" <> _ -> {
                  // Single `>` without space, skip
                  parse_test_blocks(rest, file, acc_tests, acc_errors, pending_annotation)
                }
                _ -> {
                  // Not a test line, continue
                  parse_test_blocks(rest, file, acc_tests, acc_errors, pending_annotation)
                }
              }
            }
          }
        }
      }
    }
  }
}

/// Parse test body after a test name comment.
fn parse_test_body(
  lines: List(#(Int, String)),
  file: String,
  test_name: String,
  annotations: List(Annotation),
  acc_tests: List(Test),
  acc_errors: List(SyntaxError),
) -> #(List(Test), List(SyntaxError), Option(List(Annotation))) {
  // Collect all `> ` lines for the expression
  let #(expr_lines, remaining_lines, expr_span) = collect_expression_lines(lines, file, [], None)
  
  case expr_lines {
    [] -> {
      // No expression found, error
      let error = SyntaxError(
        message: "Test name without expression",
        span: test_name_span(test_name, file),
      )
      parse_test_blocks(remaining_lines, file, acc_tests, [error, ..acc_errors], None)
    }
    
    [first, ..rest_lines] -> {
      // Combine expression lines
      let expr_source = combine_expression_lines(expr_lines)
      
      // Parse the expression
      case parse_expr_result(expr_source) {
        Ok(expression) -> {
          // Now find the expected result
          case find_expected_result(remaining_lines, file) {
            #(expected, after_expected) -> {
              case expected {
                Some(#(expected_content, expected_span)) -> {
                  // Parse expected result (pattern or expression)
                  let expected_result = parse_expected_result(expected_content, expected_span, file)

                  let parsed_test = Test(
                    name: test_name,
                    expression: expression,
                    expected: expected_result,
                    span: expr_span,
                    annotations: annotations,
                  )

                  parse_test_blocks(after_expected, file, [parsed_test, ..acc_tests], acc_errors, None)
                }
                
                None -> {
                  // No expected result found
                  let error = SyntaxError(
                    message: "Test expression without expected result",
                    span: expr_span,
                  )
                  parse_test_blocks(after_expected, file, acc_tests, [error, ..acc_errors], None)
                }
              }
            }
          }
        }
        
        Error(parse_error) -> {
          // Expression parse error
          parse_test_blocks(remaining_lines, file, acc_tests, [parse_error, ..acc_errors], None)
        }
      }
    }
  }
}

/// Parse a multi-line test: `> expr\nexpected` (no `~>` separator).
/// Collects all `> ` lines as the expression, then finds the next non-empty line as expected.
/// Returns #(Some(test), remaining_lines) on success, #(None, remaining_lines) on failure.
fn parse_multi_line_test(
  lines: List(#(Int, String)),
  file: String,
  first_line_num: Int,
  first_content: String,
  annotations: List(Annotation),
) -> #(Option(Test), List(#(Int, String))) {
  // Collect all consecutive `> ` lines
  let first = #(first_line_num, first_content)
  let #(expr_lines, remaining) = collect_all_expr_lines(lines, [first], file)

  // Combine expression lines
  let expr_source = combine_expression_lines(expr_lines)

  // Parse the expression
  case parse_expr_result(expr_source) {
    Ok(expression) -> {
      // Find expected result: skip empty lines, then take next non-comment line
      let non_empty = skip_empty_lines(remaining)
      case non_empty {
        [] -> #(None, remaining)
        [next, ..after] -> {
          let #(line_num, line_content) = next
          let trimmed = string.trim(line_content)
          // Stop if we hit a comment (test name or annotation)
          case string.starts_with(trimmed, "-- ") {
            True -> #(None, remaining)
            False -> {
              let span = Span(file, line_num, 0, line_num, string.length(line_content))
              let expected_result = parse_expected_result(trimmed, span, file)
              // Get span from first expr line
              let expr_span = Span(file, first_line_num, 0, first_line_num, 2 + string.length(first_content))
              let test_name = expr_source
              let parsed_test = Test(
                name: test_name,
                expression: expression,
                expected: expected_result,
                span: expr_span,
                annotations: annotations,
              )
              #(Some(parsed_test), after)
            }
          }
        }
      }
    }
    Error(_) -> #(None, remaining)
  }
}

/// Collect all consecutive `> ` expression lines, including the first one already collected.
fn collect_all_expr_lines(
  lines: List(#(Int, String)),
  acc: List(#(Int, String)),
  file: String,
) -> #(List(#(Int, String)), List(#(Int, String))) {
  case lines {
    [] -> #(list.reverse(acc), [])
    [line, ..rest] -> {
      let #(line_num, line_content) = line
      let trimmed = string.trim(line_content)
      case string.starts_with(trimmed, "> ") {
        True -> {
          let content = string.drop_start(trimmed, 2)
          let pair = #(line_num, content)
          collect_all_expr_lines(rest, [pair, ..acc], file)
        }
        False -> #(list.reverse(acc), lines)
      }
    }
  }
}

// ============================================================================
// LINE PARSING HELPERS
// ============================================================================

/// Parse an annotation line: `-- @name` or `-- @name value`
fn parse_annotation_line(line: String, line_num: Int, file: String) -> Option(List(Annotation)) {
  case string.starts_with(line, "-- ") {
    False -> None
    True -> {
      let content = string.drop_start(line, 3) |> string.trim
      case string.starts_with(content, "@") {
        False -> None
        True -> {
          let annotation = parse_single_annotation(content, line_num, file)
          case annotation {
            Some(a) -> Some([a])
            None -> None
          }
        }
      }
    }
  }
}

/// Parse a single annotation from `@name` or `@name value`
fn parse_single_annotation(content: String, line_num: Int, file: String) -> Option(Annotation) {
  let parts = string.split(content, " ")
  case parts {
    ["@skip"] -> Some(Skip(""))
    ["@skip", ..reason_parts] -> Some(Skip(string.join(reason_parts, " ")))
    ["@timeout", ms_str] -> {
      case int.parse(ms_str) {
        Ok(ms) -> Some(Timeout(ms))
        Error(_) -> None
      }
    }
    ["@group", name] -> Some(Group(name))
    ["@io"] -> Some(IO)
    ["@retry", count_str] -> {
      case int.parse(count_str) {
        Ok(count) -> Some(Retry(count))
        Error(_) -> None
      }
    }
    ["@requires", name] -> Some(Requires(name))
    _ -> None
  }
}

/// Parse a test name line: `-- Test name` (not starting with @)
fn parse_test_name_line(line: String, line_num: Int, file: String) -> Option(String) {
  case string.starts_with(line, "-- ") {
    False -> None
    True -> {
      let content = string.drop_start(line, 3) |> string.trim
      case string.starts_with(content, "@") {
        True -> None  // This is an annotation, not a name
        False -> {
          case content {
            "" -> None
            _ -> Some(content)
          }
        }
      }
    }
  }
}

/// Collect all consecutive `> ` lines for an expression
fn collect_expression_lines(
  lines: List(#(Int, String)),
  file: String,
  acc_lines: List(#(Int, String)),
  first_span: Option(Span),
) -> #(List(#(Int, String)), List(#(Int, String)), Span) {
  case lines {
    [] -> {
      let span = option.unwrap(first_span, Span(file, 0, 0, 0, 0))
      #(list.reverse(acc_lines), [], span)
    }

    [line, ..rest] -> {
      let #(line_num, line_content) = line
      let trimmed = string.trim(line_content)

      case string.starts_with(trimmed, "> ") {
        True -> {
          let content = string.drop_start(trimmed, 2)
          let span = Span(file, line_num, 0, line_num, string.length(line_content))
          let first = option.unwrap(first_span, span)
          collect_expression_lines(rest, file, [#(line_num, content), ..acc_lines], Some(first))
        }
        False -> {
          // End of expression lines
          let span = option.unwrap(first_span, Span(file, line_num, 0, line_num, 0))
          #(list.reverse(acc_lines), rest, span)
        }
      }
    }
  }
}

/// Combine expression lines into a single source string
fn combine_expression_lines(lines: List(#(Int, String))) -> String {
  lines
  |> list.map(fn(line) { line.1 })
  |> string.join("\n")
}

/// Find the expected result after expression lines
fn find_expected_result(
  lines: List(#(Int, String)),
  file: String,
) -> #(Option(#(String, Span)), List(#(Int, String))) {
  // Skip empty lines first
  let non_empty = skip_empty_lines(lines)
  
  case non_empty {
    [] -> #(None, [])
    
    [first, ..rest] -> {
      let #(line_num, line_content) = first
      let trimmed = string.trim(line_content)
      
      // Check if this is a new test/comment
      case string.starts_with(trimmed, "-- ") {
        True -> #(None, non_empty)  // No expected result found
        False -> {
          let span = Span(file, line_num, 0, line_num, string.length(line_content))
          #(Some(#(trimmed, span)), rest)
        }
      }
    }
  }
}

/// Skip empty lines
fn skip_empty_lines(lines: List(#(Int, String))) -> List(#(Int, String)) {
  case lines {
    [] -> []
    [line, ..rest] -> {
      let #(_, content) = line
      case string.trim(content) {
        "" -> skip_empty_lines(rest)
        _ -> [line, ..rest]
      }
    }
  }
}

/// Parse single-line test: `> expr ~> expected`
fn parse_single_line_test(
  line: String,
  line_num: Int,
  file: String,
  annotations: List(Annotation),
) -> Result(Test, SyntaxError) {
  // Remove leading `> ` if present
  let content = case string.starts_with(line, "> ") {
    True -> string.drop_start(line, 2)
    False -> line
  }
  
  // Split on `~>`
  let parts = string.split(content, "~>")
  case parts {
    [expr_str, expected_str] -> {
      let expr_trimmed = string.trim(expr_str)
      let expected_trimmed = string.trim(expected_str)
      
      // Parse expression
      case parse_expr_result(expr_trimmed) {
        Ok(expression) -> {
          // Parse expected
          let expected_span = Span(file, line_num, 0, line_num, string.length(line))
          let expected = parse_expected_result(expected_trimmed, expected_span, file)
          
          // Generate test name from expression
          let test_name = expr_trimmed
          
          Ok(Test(
            name: test_name,
            expression: expression,
            expected: expected,
            span: expected_span,
            annotations: annotations,
          ))
        }
        Error(error) -> Error(error)
      }
    }
    _ -> {
      Error(SyntaxError(
        message: "Invalid single-line test format. Use: > expression ~> expected",
        span: Span(file, line_num, 0, line_num, string.length(line)),
      ))
    }
  }
}

// ============================================================================
// EXPECTED RESULT PARSING
// ============================================================================

/// Parse expected result as pattern or expression.
fn parse_expected_result(content: String, span: Span, file: String) -> ExpectedResult {
  // Try to parse as expression first
  case parse_expr(content) {
    ParseResult(expr, []) -> {
      // Fix the spans on the expression to use the correct file and line
      let fixed_expr = fix_expr_file_span(expr, file)
      // Adjust line numbers to match the expected result's position
      // span.start_line is the line where the expected result appears in the file
      // The parsed expr will have start_line=1 (first line of parsed content)
      // So we need to add (span.start_line - 1) to get the correct line
      let line_offset = span.start_line - 1
      let adjusted = adjust_expr_spans(fixed_expr, line_offset)
      Expression(adjusted)
    }
    _ -> {
      // If it looks like a pattern (contains `_`), treat as pattern
      case string.contains(content, "_") {
        True -> Pattern(content)
        False -> Pattern(content)
      }
    }
  }
}

/// Adjust line numbers in expression spans by adding an offset.
fn adjust_expr_spans(expr: Expr, line_offset: Int) -> Expr {
  let s = get_expr_span(expr)
  let fixed = Span(
    s.file,
    s.start_line + line_offset,
    s.start_col,
    s.end_line + line_offset,
    s.end_col,
  )
  case expr {
    EInt(n, _) -> EInt(n, fixed)
    EFloat(n, _) -> EFloat(n, fixed)
    EStr(s_val, _) -> EStr(s_val, fixed)
    EVar(name, _) -> EVar(name, fixed)
    ELet(name, mutable, type_ann, value, _) ->
      ELet(name, mutable, type_ann, adjust_expr_spans(value, line_offset), fixed)
    EBlock(stmts, _) ->
      EBlock(list.map(stmts, fn(stmt) { adjust_expr_spans(stmt, line_offset) }), fixed)
    ESimpleFn(name, params, return_type, body, _) ->
      ESimpleFn(name, params, return_type, adjust_expr_spans(body, line_offset), fixed)
    EApp(fn_expr, args, _) ->
      EApp(adjust_expr_spans(fn_expr, line_offset), list.map(args, fn(a) { adjust_expr_spans(a, line_offset) }), fixed)
    ELambda(type_params, params, body, _) ->
      ELambda(type_params, params, adjust_expr_spans(body, line_offset), fixed)
    EBinOp(left, op, right, _) ->
      EBinOp(adjust_expr_spans(left, line_offset), op, adjust_expr_spans(right, line_offset), fixed)
    EUnaryOp(op, arg, _) ->
      EUnaryOp(op, adjust_expr_spans(arg, line_offset), fixed)
    EMatch(expr_val, clauses, _) ->
      EMatch(adjust_expr_spans(expr_val, line_offset), list.map(clauses, adjust_clause_spans(_, line_offset)), fixed)
    EIf(cond, then_branch, else_branch, _) ->
      EIf(
        adjust_expr_spans(cond, line_offset),
        adjust_expr_spans(then_branch, line_offset),
        case else_branch {
          Some(e) -> Some(adjust_expr_spans(e, line_offset))
          None -> None
        },
        fixed,
      )
    EFor(pattern, collection, body, _) ->
      EFor(pattern, adjust_expr_spans(collection, line_offset), list.map(body, fn(stmt) { adjust_expr_spans(stmt, line_offset) }), fixed)
    EWhile(cond, body, _) ->
      EWhile(adjust_expr_spans(cond, line_offset), list.map(body, fn(stmt) { adjust_expr_spans(stmt, line_offset) }), fixed)
    ELoop(body, _) ->
      ELoop(list.map(body, fn(stmt) { adjust_expr_spans(stmt, line_offset) }), fixed)
    EBreak(_) -> EBreak(fixed)
    EContinue(_) -> EContinue(fixed)
    ETest(name, body, _) ->
      ETest(name, adjust_expr_spans(body, line_offset), fixed)
    ERun(name, _) ->
      ERun(name, fixed)
    EImport(item, _) ->
      EImport(item, fixed)
    ECtr(name, args, _) ->
      ECtr(name, list.map(args, fn(a) { adjust_expr_spans(a, line_offset) }), fixed)
    ETypeDecl(name, type_params, constructors, _) ->
      ETypeDecl(name, type_params, constructors, fixed)
    EOverloadedFn(name, type_param, param_name, param_type, return_type, body, _) ->
      EOverloadedFn(name, type_param, param_name, param_type, return_type, adjust_expr_spans(body, line_offset), fixed)
    EOverloadedApp(name, args, _) ->
      EOverloadedApp(name, list.map(args, fn(a) { adjust_expr_spans(a, line_offset) }), fixed)
  }
}

fn adjust_clause_spans(clause: MatchClause, line_offset: Int) -> MatchClause {
  case clause {
    MatchClause(pattern: pattern, guard: guard, body: body, span: s) ->
      MatchClause(
        pattern: pattern,
        guard: case guard {
          Some(g) -> Some(adjust_expr_spans(g, line_offset))
          None -> None
        },
        body: adjust_expr_spans(body, line_offset),
        span: Span(s.file, s.start_line + line_offset, s.start_col, s.end_line + line_offset, s.end_col),
      )
  }
}

/// Fix the file in all spans of an expression.
fn fix_expr_file_span(expr: Expr, file: String) -> Expr {
  let span = get_expr_span(expr)
  let fixed = Span(file, span.start_line, span.start_col, span.end_line, span.end_col)
  case expr {
    EInt(n, _) -> EInt(n, fixed)
    EFloat(n, _) -> EFloat(n, fixed)
    EStr(s_val, _) -> EStr(s_val, fixed)
    EVar(name, _) -> EVar(name, fixed)
    ELet(name, mutable, type_ann, value, _) ->
      ELet(name, mutable, type_ann, fix_expr_file_span(value, file), fixed)
    EBlock(stmts, _) ->
      EBlock(list.map(stmts, fn(stmt) { fix_expr_file_span(stmt, file) }), fixed)
    ESimpleFn(name, params, return_type, body, _) ->
      ESimpleFn(name, params, return_type, fix_expr_file_span(body, file), fixed)
    EApp(fn_expr, args, _) ->
      EApp(fix_expr_file_span(fn_expr, file), list.map(args, fn(a) { fix_expr_file_span(a, file) }), fixed)
    ELambda(type_params, params, body, _) ->
      ELambda(type_params, params, fix_expr_file_span(body, file), fixed)
    EBinOp(left, op, right, _) ->
      EBinOp(fix_expr_file_span(left, file), op, fix_expr_file_span(right, file), fixed)
    EUnaryOp(op, arg, _) ->
      EUnaryOp(op, fix_expr_file_span(arg, file), fixed)
    EMatch(expr_val, clauses, _) ->
      EMatch(fix_expr_file_span(expr_val, file), list.map(clauses, fix_clause_file(_, file)), fixed)
    EIf(cond, then_branch, else_branch, _) ->
      EIf(
        fix_expr_file_span(cond, file),
        fix_expr_file_span(then_branch, file),
        case else_branch {
          Some(e) -> Some(fix_expr_file_span(e, file))
          None -> None
        },
        fixed,
      )
    EFor(pattern, collection, body, _) ->
      EFor(pattern, fix_expr_file_span(collection, file), list.map(body, fn(stmt) { fix_expr_file_span(stmt, file) }), fixed)
    EWhile(cond, body, _) ->
      EWhile(fix_expr_file_span(cond, file), list.map(body, fn(stmt) { fix_expr_file_span(stmt, file) }), fixed)
    ELoop(body, _) ->
      ELoop(list.map(body, fn(stmt) { fix_expr_file_span(stmt, file) }), fixed)
    EBreak(_) -> EBreak(fixed)
    EContinue(_) -> EContinue(fixed)
    ETest(name, body, _) ->
      ETest(name, fix_expr_file_span(body, file), fixed)
    ERun(name, _) ->
      ERun(name, fixed)
    EImport(item, _) ->
      EImport(item, fixed)
    ECtr(name, args, _) ->
      ECtr(name, list.map(args, fn(a) { fix_expr_file_span(a, file) }), fixed)
    ETypeDecl(name, type_params, constructors, _) ->
      ETypeDecl(name, type_params, constructors, fixed)
    EOverloadedFn(name, type_param, param_name, param_type, return_type, body, _) ->
      EOverloadedFn(name, type_param, param_name, param_type, return_type, fix_expr_file_span(body, file), fixed)
    EOverloadedApp(name, args, _) ->
      EOverloadedApp(name, list.map(args, fn(a) { fix_expr_file_span(a, file) }), fixed)
  }
}

/// Get the span from an expression.
fn get_expr_span(expr: Expr) -> Span {
  case expr {
    EInt(_, s) -> s
    EFloat(_, s) -> s
    EStr(_, s) -> s
    EVar(_, s) -> s
    ELet(_, _, _, _, s) -> s
    EBlock(_, s) -> s
    ESimpleFn(_, _, _, _, s) -> s
    EApp(_, _, s) -> s
    ELambda(_, _, _, s) -> s
    EBinOp(_, _, _, s) -> s
    EUnaryOp(_, _, s) -> s
    EMatch(_, _, s) -> s
    EIf(_, _, _, s) -> s
    EFor(_, _, _, s) -> s
    EWhile(_, _, s) -> s
    ELoop(_, s) -> s
    EBreak(s) -> s
    EContinue(s) -> s
    ETest(_, _, s) -> s
    ERun(_, s) -> s
    EImport(_, s) -> s
    ECtr(_, _, s) -> s
    ETypeDecl(_, _, _, s) -> s
    EOverloadedFn(_, _, _, _, _, _, s) -> s
    EOverloadedApp(_, _, s) -> s
  }
}

fn fix_clause_file(clause: MatchClause, file: String) -> MatchClause {
  case clause {
    MatchClause(pattern: pattern, guard: guard, body: body, span: s) ->
      MatchClause(
        pattern: pattern,
        guard: case guard {
          Some(g) -> Some(fix_expr_file_span(g, file))
          None -> None
        },
        body: fix_expr_file_span(body, file),
        span: Span(file, s.start_line, s.start_col, s.end_line, s.end_col),
      )
  }
}

fn fix_expected_file(expected: ExpectedResult, file: String) -> ExpectedResult {
  case expected {
    Pattern(p) -> Pattern(p)
    Expression(expr) -> Expression(fix_expr_file_span(expr, file))
  }
}

// ============================================================================
// ANNOTATION HELPERS
// ============================================================================

/// Merge new annotations with pending annotations
fn merge_annotations(
  pending: Option(List(Annotation)),
  new: List(Annotation),
) -> List(Annotation) {
  case pending {
    None -> new
    Some(existing) -> list.append(existing, new)
  }
}

/// Create a span for a test name
fn test_name_span(name: String, file: String) -> Span {
  Span(file, 0, 0, 0, string.length(name))
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/// Parse an expression using the Tao parser
fn parse_expr_result(source: String) -> Result(Expr, SyntaxError) {
  case parse_expr(source) {
    ParseResult(ast, []) -> Ok(ast)
    ParseResult(_, errors) -> Error(SyntaxError(
      message: "Parse error: " <> int.to_string(list.length(errors)) <> " errors",
      span: Span("unknown", 0, 0, 0, 0),
    ))
  }
}
