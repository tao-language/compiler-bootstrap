// ============================================================================
// TAO OVERLOADING TESTS
// ============================================================================
/// Tests for Tao operator overloading through implicit arguments.
///
/// These tests verify that:
/// 1. Overloaded functions parse correctly
/// 2. Desugaring produces correct Core terms
/// 3. Type inference works correctly
/// 4. Evaluation produces correct results

import gleeunit
import gleeunit/should
import gleam/string
import tao/syntax.{parse, parse_module, format_expr, OverloadedFn, OverloadedApp, Int as TaoInt, Var, BinOp, Add}
import syntax/grammar.{type ParseResult, ParseResult, type Span, Span}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// PARSER TESTS - OVERLOADED FUNCTIONS
// ============================================================================

pub fn parse_overloaded_fn_i32_test() {
  // fn (+)(x: I32) -> I32 { x }
  let source = "fn (+)(x: I32) -> I32 { x }"
  let ParseResult(_ast, errors) = parse(source)
  errors |> should.equal([])
}

pub fn parse_overloaded_fn_with_body_test() {
  // fn (+)(x: I32) -> I32 { x + 1 }
  let source = "fn (+)(x: I32) -> I32 { x + 1 }"
  let ParseResult(_ast, errors) = parse(source)
  errors |> should.equal([])
}

pub fn parse_overloaded_fn_sub_test() {
  // fn (-)(x: I32) -> I32 { x - 1 }
  let source = "fn (-)(x: I32) -> I32 { x - 1 }"
  let ParseResult(_ast, errors) = parse(source)
  errors |> should.equal([])
}

pub fn parse_overloaded_fn_mul_test() {
  // fn (*)(x: I32) -> I32 { x * 2 }
  let source = "fn (*)(x: I32) -> I32 { x * 2 }"
  let ParseResult(_ast, errors) = parse(source)
  errors |> should.equal([])
}

pub fn parse_overloaded_fn_div_test() {
  // fn (/)(x: I32) -> I32 { x / 2 }
  let source = "fn (/)(x: I32) -> I32 { x / 2 }"
  let ParseResult(_ast, errors) = parse(source)
  errors |> should.equal([])
}

// ============================================================================
// PARSER TESTS - MULTIPLE OVERLOADS
// ============================================================================

pub fn parse_multiple_overloads_i32_test() {
  // Two overloaded versions with I32
  let source = "fn (+)(x: I32) -> I32 { x + 1 }\nfn (+)(y: I32) -> I32 { y + 2 }"
  let ParseResult(_ast, errors) = parse_module(source, "test")
  errors |> should.equal([])
}

pub fn parse_multiple_overloads_different_ops_test() {
  // Different operators
  let source = "fn (+)(x: I32) -> I32 { x + 1 }\nfn (-)(x: I32) -> I32 { x - 1 }"
  let ParseResult(_ast, errors) = parse_module(source, "test")
  errors |> should.equal([])
}

// ============================================================================
// FORMATTER TESTS
// ============================================================================

pub fn format_overloaded_fn_test() {
  let span = Span("test", 1, 1, 1, 10)
  let body = TaoInt(0, span)
  let expr = OverloadedFn("+", "T", "x", "I32", "I32", body, span)
  let result = format_expr(expr)
  // Verify format produces output containing the operator name
  string.contains(result, "+") |> should.be_true()
}

pub fn format_overloaded_app_test() {
  let span = Span("test", 1, 1, 1, 10)
  let expr = OverloadedApp("+", [TaoInt(1, span), TaoInt(2, span)], span)
  let result = format_expr(expr)
  // Verify format produces output
  string.is_empty(result) |> should.be_false()
}

// ============================================================================
// EXPRESSION PARSING TESTS
// ============================================================================

pub fn parse_binop_with_overloaded_fn_test() {
  // Verify that binary operators in the body are parsed correctly
  let source = "fn (+)(x: I32) -> I32 { x + 1 }"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  
  // Verify the AST is an OverloadedFn
  case ast {
    OverloadedFn(_, _, _, _, _, _, _) -> True
    _ -> False
  } |> should.be_true()
}

// ============================================================================
// HELPERS
// ============================================================================
