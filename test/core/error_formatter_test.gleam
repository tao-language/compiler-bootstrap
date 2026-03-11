import core/core.{type Error, TypeMismatch, VarUndefined, HoleUnsolved, VTyp, VLitT, I32T, F64T}
import core/error_formatter
import core/color.{default_config, no_color}
import gleam/string
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TYPE MISMATCH ERROR TEST
// ============================================================================

pub fn test_format_type_mismatch() {
  let span1 = Span("test.core", 3, 5, 3, 10)
  let span2 = Span("test.core", 3, 12, 3, 15)
  let error = TypeMismatch(VTyp(0), VTyp(1), span1, span2)
  let source = "let x: Int = 3.14"

  let result = error_formatter.format_error(error, source, "test.core")

  // Check that the result contains key elements
  string.contains(result, "error[E0101]")
  |> should.equal(True)

  string.contains(result, "Type mismatch")
  |> should.equal(True)
}

// ============================================================================
// UNDEFINED VARIABLE ERROR TEST
// ============================================================================

pub fn test_format_var_undefined() {
  let span = Span("test.core", 5, 3, 5, 8)
  let error = VarUndefined(0, span)
  let source = "  count + 1"

  let result = error_formatter.format_error(error, source, "test.core")

  string.contains(result, "error[E0102]")
  |> should.equal(True)

  string.contains(result, "Undefined variable")
  |> should.equal(True)

  string.contains(result, "not defined in this scope")
  |> should.equal(True)
}

// ============================================================================
// HOLE UNSOLVED ERROR TEST
// ============================================================================

pub fn test_format_hole_unsolved() {
  let span = Span("test.core", 10, 1, 10, 2)
  let error = HoleUnsolved(1, span)
  let source = "  ?"

  let result = error_formatter.format_error(error, source, "test.core")

  string.contains(result, "error[E0106]")
  |> should.equal(True)

  string.contains(result, "Unsolved hole")
  |> should.equal(True)

  string.contains(result, "Hole #1")
  |> should.equal(True)
}

// ============================================================================
// COLOR CONFIGURATION TEST
// ============================================================================

pub fn test_format_with_colors_enabled() {
  let span1 = Span("test.core", 3, 5, 3, 10)
  let span2 = Span("test.core", 3, 12, 3, 15)
  let error = TypeMismatch(VLitT(I32T), VLitT(F64T), span1, span2)
  let source = "let x: Int = 3.14"

  let result = error_formatter.format_error_with_config(
    error,
    source,
    "test.core",
    default_config,
  )

  // With colors enabled, should contain ANSI codes
  string.contains(result, "\u{1b}[")
  |> should.equal(True)
}

pub fn test_format_with_colors_disabled() {
  let span1 = Span("test.core", 3, 5, 3, 10)
  let span2 = Span("test.core", 3, 12, 3, 15)
  let error = TypeMismatch(VLitT(I32T), VLitT(F64T), span1, span2)
  let source = "let x: Int = 3.14"

  let result = error_formatter.format_error_with_config(
    error,
    source,
    "test.core",
    no_color,
  )

  // With colors disabled, should not contain ANSI codes
  string.contains(result, "\u{1b}[")
  |> should.equal(False)

  // But should still contain the error message
  string.contains(result, "error[E0101]")
  |> should.equal(True)

  string.contains(result, "Type mismatch")
  |> should.equal(True)
}

// ============================================================================
// ERROR CODES TEST
// ============================================================================

pub fn test_error_codes() {
  // Test various error codes
  let span = Span("test.core", 1, 1, 1, 5)

  error_formatter.error_code(TypeMismatch(VTyp(0), VTyp(1), span, span))
  |> should.equal("E0101")

  error_formatter.error_code(VarUndefined(0, span))
  |> should.equal("E0102")

  error_formatter.error_code(HoleUnsolved(1, span))
  |> should.equal("E0106")
}

// ============================================================================
// ERROR MESSAGES TEST
// ============================================================================

pub fn test_error_messages() {
  let span = Span("test.core", 1, 1, 1, 5)

  error_formatter.error_message(TypeMismatch(VTyp(0), VTyp(1), span, span))
  |> should.equal("Type mismatch")

  error_formatter.error_message(VarUndefined(0, span))
  |> should.equal("Undefined variable")

  error_formatter.error_message(HoleUnsolved(1, span))
  |> should.equal("Unsolved hole")
}
