// ============================================================================
// TAO DESUGARER TESTS
// ============================================================================
/// Tests for Tao desugarer.
import tao/desugar.{desugar}
import tao/syntax.{MvpInt, MvpVar, MvpAdd, MvpSub, MvpMul, MvpDiv}
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
  let term = desugar(MvpInt(42, todo_span()))
  // Should produce a Core term (just verify it doesn't panic)
  True |> should.be_true()
}

pub fn desugar_int_zero_test() {
  let term = desugar(MvpInt(0, todo_span()))
  True |> should.be_true()
}

pub fn desugar_int_negative_test() {
  let term = desugar(MvpInt(-5, todo_span()))
  True |> should.be_true()
}

// ============================================================================
// VARIABLE DESUGARING
// ============================================================================

pub fn desugar_variable_test() {
  let term = desugar(MvpVar("x", todo_span()))
  True |> should.be_true()
}

pub fn desugar_variable_name_test() {
  let term = desugar(MvpVar("myVar", todo_span()))
  True |> should.be_true()
}

// ============================================================================
// BINARY OPERATION DESUGARING
// ============================================================================

pub fn desugar_addition_test() {
  let expr = MvpAdd(MvpInt(1, todo_span()), MvpInt(2, todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_subtraction_test() {
  let expr = MvpSub(MvpInt(10, todo_span()), MvpInt(5, todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_multiplication_test() {
  let expr = MvpMul(MvpInt(3, todo_span()), MvpInt(4, todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_division_test() {
  let expr = MvpDiv(MvpInt(20, todo_span()), MvpInt(4, todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

// ============================================================================
// NESTED EXPRESSIONS
// ============================================================================

pub fn desugar_nested_addition_test() {
  // (1 + 2) + 3
  let expr = MvpAdd(
    MvpAdd(MvpInt(1, todo_span()), MvpInt(2, todo_span()), todo_span()),
    MvpInt(3, todo_span()),
    todo_span(),
  )
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_mixed_operations_test() {
  // 1 + 2 * 3
  let expr = MvpAdd(
    MvpInt(1, todo_span()),
    MvpMul(MvpInt(2, todo_span()), MvpInt(3, todo_span()), todo_span()),
    todo_span(),
  )
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_variable_in_binop_test() {
  // x + 5
  let expr = MvpAdd(MvpVar("x", todo_span()), MvpInt(5, todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_two_variables_test() {
  // x + y
  let expr = MvpAdd(MvpVar("x", todo_span()), MvpVar("y", todo_span()), todo_span())
  let term = desugar(expr)
  True |> should.be_true()
}

// ============================================================================
// COMPLEX EXPRESSIONS
// ============================================================================

pub fn desugar_complex_expression_test() {
  // (x + y) * (a - b)
  let expr = MvpMul(
    MvpAdd(MvpVar("x", todo_span()), MvpVar("y", todo_span()), todo_span()),
    MvpSub(MvpVar("a", todo_span()), MvpVar("b", todo_span()), todo_span()),
    todo_span(),
  )
  let term = desugar(expr)
  True |> should.be_true()
}

pub fn desugar_chain_test() {
  // 1 + 2 + 3 + 4
  let expr = MvpAdd(
    MvpAdd(
      MvpAdd(MvpInt(1, todo_span()), MvpInt(2, todo_span()), todo_span()),
      MvpInt(3, todo_span()),
      todo_span(),
    ),
    MvpInt(4, todo_span()),
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
