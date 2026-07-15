/// Error types and human-readable display for the compiler.
///
/// Each error variant carries `Span` location information so that
/// `display` can produce messages in the familiar
/// `file:line:col: message` format with additional context.
///
/// Errors are wrapped in `ScopedError` which captures the breadcrumb
/// trail showing the path through the program structure that led to
/// the error. This helps users understand *where* and *why* an error
/// occurred.
import core/ast
import core/ffi.{type FFI}
import core/format
import core/term as tm
import core/value.{type Neut, type Value, type Variant} as v
import gleam/int
import gleam/list
import gleam/string
import syntax/span.{type Span}

// ============================================================================
// ERROR TYPE
// ============================================================================

pub type Error {
  Error(data: ErrorData, span: Span, trace: List(#(String, Span)))
}

pub type ErrorData {
  UnexpectedToken(token: String)
  VarUndefined(name: String)
  TypeMismatch(a: ast.Expr, b: ast.Expr)
  NeutralTypeMismatch(a: #(Neut, Span), b: #(Neut, Span))
  RcdFieldNotFound(field: #(String, Span))
  CallArityMismatch(#(Int, Span), #(Int, Span))
  InfiniteType(hole_id: Int, type_: Value)
  NotAFunction(fun: tm.Term, fun_type: Value)
  AppExpectedExplicitArg(fun_type: Value)
  TypeVariantUndefined(
    tag: #(String, Span),
    variants: #(List(#(String, Variant)), Span),
  )
}

// ============================================================================
// DISPLAY
// ============================================================================

/// Format an error as a human-readable string.
///
/// The output follows the convention:
///
///     path/to/file:line:col: one-line summary
///     ┌─ additional context
///     │ ...
///
/// Pass `ffi` and `types` from the context so that values and terms
/// can be formatted with proper names (De Bruijn indices → variable names).
///
/// This version accepts a raw `Error` (no breadcrumbs).
pub fn display(ffi: FFI, types: List(#(String, Value)), err: Error) -> String {
  let names = list.map(types, fn(t) { t.0 })
  let fmt_expr = fn(expr: ast.Expr) { format.expr(expr, 60, 0) }
  let fmt_value = fn(val: Value) { format.value(ffi, names, val, 60, 0) }
  let fmt_term = fn(term: tm.Term) { format.term(names, term, 60, 0) }

  case err.data {
    UnexpectedToken(token) -> {
      summary(err.span, "unexpected token: \"" <> token <> "\"")
      <> display_trace(err.trace)
    }

    VarUndefined(name) -> {
      summary(err.span, "undefined variable")
      <> display_trace(err.trace)
      <> detail(
        "The variable `" <> name <> "` has not been defined in this scope.",
      )
    }

    TypeMismatch(got, expected) -> {
      summary(got.span, "type mismatch")
      <> display_trace(err.trace)
      <> detail("Expected:   " <> fmt_expr(expected))
      <> detail("Got:        " <> fmt_expr(got))
    }

    NeutralTypeMismatch(#(neut1, span1), #(neut2, span2)) -> {
      let names = list.map(types, fn(entry) { entry.0 })
      summary(span1, "type mismatch between neutral terms")
      <> display_trace(err.trace)
      <> detail("Left:  " <> neut_to_string(ffi, names, neut1))
      <> detail("Right: " <> neut_to_string(ffi, names, neut2))
      <> case span1.file == span2.file && span1.start_line != span2.start_line {
        True ->
          detail("")
          <> detail("Right type originates at " <> span_location(span2))
        False -> ""
      }
    }

    RcdFieldNotFound(#(name, _field_span)) -> {
      summary(err.span, "record field not found: \"" <> name <> "\"")
      <> display_trace(err.trace)
    }

    CallArityMismatch(#(got_arity, span), #(expected_arity, _)) -> {
      summary(span, "call arity mismatch")
      <> display_trace(err.trace)
      <> detail("Expected " <> int.to_string(expected_arity) <> " argument(s)")
      <> detail("Got " <> int.to_string(got_arity) <> " argument(s)")
    }

    InfiniteType(hole_id, type_) -> {
      summary(err.span, "infinite type")
      <> display_trace(err.trace)
      <> detail(
        "Type hole ?"
        <> int.to_string(hole_id)
        <> " would be unified with a type that contains itself.",
      )
      <> detail("")
      <> detail("Type value: " <> fmt_value(type_))
      <> detail("")
      <> detail("This usually happens when a recursive type is not properly")
      <> detail("wrapped behind a constructor or newtype.")
    }

    NotAFunction(fun, fun_type) -> {
      summary(err.span, "not a function")
      <> display_trace(err.trace)
      <> detail("This expression has type " <> fmt_value(fun_type))
      <> detail("")
      <> detail("Term: " <> fmt_term(fun))
      <> detail("")
      <> detail(
        "You cannot apply a non-function value as if it were a function.",
      )
    }

    AppExpectedExplicitArg(fun_type) -> {
      summary(err.span, "expected explicit argument, got implicit argument")
      <> display_trace(err.trace)
      <> detail("The function type is: " <> fmt_value(fun_type))
      <> detail("")
      <> detail("Use `f(arg)` for explicit arguments, not `f<arg>`.")
    }

    TypeVariantUndefined(#(tag, tag_span), #(variants, type_span)) -> {
      let variant_names = list.map(variants, fn(vr) { vr.0 })
      summary(tag_span, "undefined variant `" <> tag <> "`")
      <> display_trace(err.trace)
      <> detail(
        "This type has the variants: " <> string.join(variant_names, ", "),
      )
      <> case
        type_span.file == tag_span.file
        && type_span.start_line != tag_span.start_line
      {
        True ->
          detail("")
          <> detail("The type definition is at " <> span_location(type_span))
        False -> ""
      }
      <> detail("")
      <> detail(
        "Did you mean one of: " <> string.join(variant_names, ", ") <> "?",
      )
    }
  }
}

/// Render the breadcrumb trail as a tree.
pub fn display_trace(trace: List(#(String, Span))) -> String {
  list.map(trace, fn(entry) {
    let #(label, span) = entry
    "\n      in \"" <> label <> "\" (" <> span_short(span) <> ")"
  })
  |> string.join("")
}

/// Format a span concisely as "file:line:col".
fn span_short(span: Span) -> String {
  span.file
  <> ":"
  <> int.to_string(span.start_line)
  <> ":"
  <> int.to_string(span.start_col)
}

// ============================================================================
// NEUTRAL VALUE FORMATTING
// ============================================================================

/// Format a `Neut` (neutral value) as a human-readable string.
///
/// Neutral values (unsolved holes, free variables, unresolved applications)
/// have no named representation in the context, so we format them directly
/// without going through `format.value`.
fn neut_to_string(ffi: FFI, names: List(String), neut: Neut) -> String {
  let value = v.Neut(neut)
  format.value(ffi, names, value, 60, 2)
}

// ============================================================================
// SPAN FORMATTING
// ============================================================================

/// Format `file:line:col` for the summary line.
fn span_header(span: Span) -> String {
  span.file
  <> ":"
  <> int.to_string(span.start_line)
  <> ":"
  <> int.to_string(span.start_col)
}

/// Format a more descriptive location: `file line N, col M`.
fn span_location(span: Span) -> String {
  case span.start_line == span.end_line {
    True ->
      span.file
      <> " line "
      <> int.to_string(span.start_line)
      <> ", col "
      <> int.to_string(span.start_col)
    False ->
      span.file
      <> " lines "
      <> int.to_string(span.start_line)
      <> "-"
      <> int.to_string(span.end_line)
      <> ", col "
      <> int.to_string(span.start_col)
  }
}

/// Build the one-line summary: `file:line:col: message`
fn summary(span: Span, message: String) -> String {
  span_header(span) <> ": " <> message
}

/// Build a detail line prefixed with `  ` (two spaces).
fn detail(line: String) -> String {
  "\n  " <> line
}
