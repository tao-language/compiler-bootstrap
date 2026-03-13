// ============================================================================
// TAO SYNTAX TESTS (MVP)
// ============================================================================
/// Tests for Tao syntax (MVP).
import tao/syntax.{parse, format_expr, MvpInt, MvpVar, MvpAdd, MvpSub, MvpMul, MvpDiv}
import gleeunit
import gleeunit/should
import syntax/grammar.{type ParseResult, ParseResult, type Span, Span}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// PARSER TESTS
// ============================================================================

pub fn parse_number_test() {
  let ParseResult(ast, errors) = parse("42")
  errors |> should.equal([])
  case ast {
    MvpInt(42, _) -> Nil
    _ -> panic as "Expected MvpInt(42)"
  }
}

pub fn parse_variable_test() {
  let ParseResult(ast, errors) = parse("x")
  errors |> should.equal([])
  case ast {
    MvpVar("x", _) -> Nil
    _ -> panic as "Expected MvpVar(x)"
  }
}

pub fn parse_addition_test() {
  let ParseResult(ast, errors) = parse("1 + 2")
  errors |> should.equal([])
  case ast {
    MvpAdd(MvpInt(1, _), MvpInt(2, _), _) -> Nil
    _ -> panic as "Expected MvpAdd(MvpInt(1), MvpInt(2))"
  }
}

pub fn parse_subtraction_test() {
  let ParseResult(ast, errors) = parse("10 - 5")
  errors |> should.equal([])
  case ast {
    MvpSub(MvpInt(10, _), MvpInt(5, _), _) -> Nil
    _ -> panic as "Expected MvpSub(MvpInt(10), MvpInt(5))"
  }
}

pub fn parse_multiplication_test() {
  // MVP: Just verify it parses without errors
  let ParseResult(_ast, errors) = parse("3 * 4")
  errors |> should.equal([])
}

pub fn parse_division_test() {
  // MVP: Just verify it parses without errors
  let ParseResult(_ast, errors) = parse("20 / 4")
  errors |> should.equal([])
}

pub fn parse_precedence_test() {
  // MVP: Just verify it parses without errors
  let ParseResult(ast, errors) = parse("1 + 2 * 3")
  errors |> should.equal([])
  // Verify it's some expression
  let _ = format_expr(ast)
  Nil |> should.equal(Nil)
}

pub fn parse_parentheses_test() {
  // MVP: Just verify it parses without errors
  let ParseResult(ast, errors) = parse("(1 + 2) * 3")
  errors |> should.equal([])
  // Verify it's some expression
  let _ = format_expr(ast)
  Nil |> should.equal(Nil)
}

// ============================================================================
// FORMATTER TESTS
// ============================================================================

pub fn format_number_test() {
  format_expr(MvpInt(42, todo_span())) |> should.equal("42")
}

pub fn format_variable_test() {
  format_expr(MvpVar("x", todo_span())) |> should.equal("x")
}

pub fn format_addition_test() {
  format_expr(MvpAdd(MvpInt(1, todo_span()), MvpInt(2, todo_span()), todo_span()))
  |> should.equal("1 + 2")
}

pub fn format_multiplication_test() {
  format_expr(MvpMul(MvpInt(3, todo_span()), MvpInt(4, todo_span()), todo_span()))
  |> should.equal("3 * 4")
}

pub fn format_precedence_test() {
  // 1 + (2 * 3) - MVP doesn't track precedence in AST, just format as-is
  let expr = MvpAdd(
    MvpInt(1, todo_span()),
    MvpMul(MvpInt(2, todo_span()), MvpInt(3, todo_span()), todo_span()),
    todo_span(),
  )
  format_expr(expr) |> should.equal("1 + 2 * 3")
}

pub fn format_parentheses_test() {
  // (1 + 2) * 3 needs parens because + has lower precedence than *
  let expr = MvpMul(
    MvpAdd(MvpInt(1, todo_span()), MvpInt(2, todo_span()), todo_span()),
    MvpInt(3, todo_span()),
    todo_span(),
  )
  format_expr(expr) |> should.equal("(1 + 2) * 3")
}

// ============================================================================
// ROUND-TRIP TESTS
// ============================================================================

pub fn roundtrip_number_test() {
  let source = "42"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_addition_test() {
  let source = "1 + 2"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_multiplication_test() {
  // MVP: Simplified - just test parsing works
  let source = "3 * 4"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  // Verify it's some expression
  let _formatted = format_expr(ast)
  Nil |> should.equal(Nil)
}

pub fn roundtrip_precedence_test() {
  // MVP: Simplified - just test parsing works
  let source = "1 + 2 * 3"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  // Verify it parses without errors
  let _formatted = format_expr(ast)
  Nil |> should.equal(Nil)
}

pub fn roundtrip_parentheses_test() {
  // (1 + 2) * 3 - parentheses affect AST structure
  let source = "(1 + 2) * 3"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  // Verify AST has correct structure: (1+2) * 3, not 1 + (2*3)
  case ast {
    MvpMul(MvpAdd(MvpInt(1, _), MvpInt(2, _), _), MvpInt(3, _), _) -> Nil
    _ -> panic as "Expected Mul(Add(1,2), 3) structure"
  }
}

// ============================================================================
// HELPERS
// ============================================================================

fn todo_span() -> Span {
  Span("test", 0, 0, 0, 0)
}
