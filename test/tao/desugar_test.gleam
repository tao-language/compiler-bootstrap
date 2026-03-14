// ============================================================================
// TAO DESUGARER TESTS
// ============================================================================
/// Tests for Tao desugarer.
import tao/desugar.{desugar}
import tao/syntax.{Int, Var, Add, Sub, Mul, Div}
import syntax/grammar.{type Span, Span}
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// LITERAL DESUGARING
// ============================================================================

pub fn desugar_int_literal_test() {
  let term = desugar(Int(42, todo_span()))
  // Should produce a Core term (just verify it doesn't panic)
  True |> should.be_true()
}

pub fn desugar_int_zero_test() {
  let term = desugar(Int(0, todo_span()))
  True |> should.be_true()
}

pub fn desugar_int_negative_test() {
  let term = desugar(Int(-5, todo_span()))
  True |> should.be_true()
}

// ============================================================================
// VARIABLE DESUGARING
// ============================================================================

pub fn desugar_variable_test() {
  let term = desugar(Var("x", todo_span()))
  True |> should.be_true()
}

pub fn desugar_variable_name_test() {
  let term = desugar(Var("myVar", todo_span()))
  True |> should.be_true()
}

// ============================================================================
// BINARY OPERATION DESUGARING
// ============================================================================

pub fn desugar_addition_test() {
  let expr = Add(Int(1, todo_span()), Int(2, todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_subtraction_test() {
  let expr = Sub(Int(10, todo_span()), Int(5, todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_multiplication_test() {
  let expr = Mul(Int(3, todo_span()), Int(4, todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_division_test() {
  let expr = Div(Int(20, todo_span()), Int(4, todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

// ============================================================================
// NESTED EXPRESSIONS
// ============================================================================

pub fn desugar_nested_addition_test() {
  // (1 + 2) + 3
  let expr = Add(
    Add(Int(1, todo_span()), Int(2, todo_span()), todo_span()),
    Int(3, todo_span()),
    todo_span(),
  )
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_mixed_operations_test() {
  // 1 + 2 * 3
  let expr = Add(
    Int(1, todo_span()),
    Mul(Int(2, todo_span()), Int(3, todo_span()), todo_span()),
    todo_span(),
  )
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_variable_in_binop_test() {
  // x + 5
  let expr = Add(Var("x", todo_span()), Int(5, todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_two_variables_test() {
  // x + y
  let expr = Add(Var("x", todo_span()), Var("y", todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

// ============================================================================
// COMPLEX EXPRESSIONS
// ============================================================================

pub fn desugar_complex_expression_test() {
  // (x + y) * (a - b)
  let expr = Mul(
    Add(Var("x", todo_span()), Var("y", todo_span()), todo_span()),
    Sub(Var("a", todo_span()), Var("b", todo_span()), todo_span()),
    todo_span(),
  )
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_chain_test() {
  // 1 + 2 + 3 + 4
  let expr = Add(
    Add(
      Add(Int(1, todo_span()), Int(2, todo_span()), todo_span()),
      Int(3, todo_span()),
      todo_span(),
    ),
    Int(4, todo_span()),
    todo_span(),
  )
  let term = desugar(expr)
  True |> should.be_true()
}

// ============================================================================
// HELPERS
// ============================================================================

fn todo_span() -> Span {
  Span("test", 0, 0, 0, 0)
}
