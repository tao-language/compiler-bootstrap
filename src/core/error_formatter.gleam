// ============================================================================
// CORE ERROR FORMATTER
// ============================================================================
/// Tao-style error messages with emoji-guided navigation and visual hierarchy.
///
/// Produces output like:
/// ```
/// ❌ error[E0101]: Type mismatch
///    ┌─ src/file.core:3:5
///    │
///  3 │ (x : $I32) -> x
///    │     ━━━━━ expected $Type, found $I32
///    │
///    💡 expected because this is $Type
///    📝 note: $Type and $I32 are incompatible types
///    🔧 help: use a type annotation or check your term
/// ```
import core/core.{
  type Error, type Type, type Pattern, type Value as Val, type LiteralType,
  type Literal, type Head, type Permission, type Term,
  TypeMismatch, PatternMismatch, NotAFunction, VarUndefined, HoleUnsolved,
  ArityMismatch, CtrUndefined, MatchRedundantCase, MatchMissingCase,
  ComptimePermissionDenied, InfiniteType, TypeAnnotationNeeded,
  RcdMissingFields, CtrUnsolvedParam, DotFieldNotFound, DotOnNonCtr,
  SpineMismatch, TODO,
  PAny, PAs, PTyp, PLit, PLitT, PRcd, PCtr,
  HVar, HHole,
  VTyp, VLit, VLitT, VNeut, VRcd, VCtr, VLam, VPi, VCall, VFix, VErr,
  I32, I64, U32, U64, F32, F64,
  I32T, I64T, U32T, U64T, F32T, F64T,
  AllowRead, AllowWrite,
}
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string
import syntax/grammar.{type Span}
import syntax/source_snippet.{type Diagnostic, type Highlight, type HighlightStyle, Error, Warning, Info, Span, Secondary}

// ============================================================================
// EMOJI CONSTANTS
// ============================================================================

const emoji_error = "❌"
const emoji_warning = "⚠️"
const emoji_info = "ℹ️"
const emoji_tip = "💡"
const emoji_note = "📝"
const emoji_help = "🔧"
const emoji_reference = "📚"
const emoji_target = "🎯"
const emoji_context = "🔍"
const emoji_success = "✅"

// ============================================================================
// ERROR CODES
// ============================================================================

pub fn error_code(error: Error) -> String {
  case error {
    TypeMismatch(..) -> "E0101"
    VarUndefined(..) -> "E0102"
    NotAFunction(..) -> "E0103"
    ArityMismatch(..) -> "E0104"
    CtrUndefined(..) -> "E0105"
    HoleUnsolved(..) -> "E0106"
    MatchMissingCase(..) -> "E0201"
    MatchRedundantCase(..) -> "E0202"
    PatternMismatch(..) -> "E0203"
    ComptimePermissionDenied(..) -> "E0502"
    InfiniteType(..) -> "E0107"
    TypeAnnotationNeeded(..) -> "E0108"
    RcdMissingFields(..) -> "E0109"
    CtrUnsolvedParam(..) -> "E0110"
    DotFieldNotFound(..) -> "E0111"
    DotOnNonCtr(..) -> "E0112"
    SpineMismatch(..) -> "E0113"
    TODO(..) -> "E9999"
  }
}

pub fn error_message(error: Error) -> String {
  case error {
    TypeMismatch(..) -> "Type mismatch"
    VarUndefined(..) -> "Undefined variable"
    NotAFunction(..) -> "Cannot call non-function value"
    ArityMismatch(..) -> "Wrong number of arguments"
    CtrUndefined(..) -> "Constructor not found"
    HoleUnsolved(..) -> "Unsolved hole"
    MatchMissingCase(..) -> "Pattern match not exhaustive"
    MatchRedundantCase(..) -> "Redundant pattern"
    PatternMismatch(..) -> "Pattern type mismatch"
    ComptimePermissionDenied(..) -> "Permission denied"
    InfiniteType(..) -> "Infinite type"
    TypeAnnotationNeeded(..) -> "Type annotation needed"
    RcdMissingFields(..) -> "Missing record fields"
    CtrUnsolvedParam(..) -> "Constructor parameter unsolved"
    DotFieldNotFound(..) -> "Field not found"
    DotOnNonCtr(..) -> "Cannot access field on non-record"
    SpineMismatch(..) -> "Function application mismatch"
    TODO(..) -> "TODO: Not yet implemented"
  }
}

// ============================================================================
// ERROR TO DIAGNOSTIC
// ============================================================================

pub fn error_to_diagnostic(error: Error, source: String, file: String) -> Diagnostic {
  let code = error_code(error)
  let message = error_message(error)
  let severity = source_snippet.Error

  case error {
    TypeMismatch(expected, got, span1, span2) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span1),
        spans: [
          source_snippet.Highlight(
            span: to_source_span(span2),
            style: source_snippet.Secondary,
            label: Some("expected " <> type_to_string(expected) <> ", found " <> type_to_string(got)),
          ),
        ],
        notes: [
          type_to_string(expected) <> " and " <> type_to_string(got) <> " are incompatible types",
        ],
        hints: type_mismatch_hints(expected, got, source, span1),
      )

    VarUndefined(index, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: ["Variable at index " <> int.to_string(index) <> " is not defined in this scope"],
        hints: [
          "Check variable name and scope",
          "Did you forget to define this variable?",
        ],
      )

    NotAFunction(fun, fun_ty) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(fun.span),
        spans: [],
        notes: [
          "This value has type " <> type_to_string(fun_ty) <> ", which is not callable",
        ],
        hints: [
          "Only functions can be called with parentheses",
          "Check that you're calling a function, not a value",
        ],
      )

    ArityMismatch(span1, span2) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span1),
        spans: [
          source_snippet.Highlight(
            span: to_source_span(span2),
            style: source_snippet.Secondary,
            label: Some("function defined here"),
          ),
        ],
        notes: ["Expected a different number of arguments"],
        hints: [
          "Check the function signature and provide the correct number of arguments",
        ],
      )

    CtrUndefined(tag, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: ["Constructor `" <> tag <> "` is not defined"],
        hints: [
          "Check the constructor name for typos",
          "Make sure the constructor is defined in the current scope",
        ],
      )

    HoleUnsolved(id, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: ["Hole #" <> int.to_string(id) <> " was not solved during type checking"],
        hints: [
          "Holes are placeholders that must be filled",
          "Provide a term of the expected type, or add a type annotation",
        ],
      )

    MatchMissingCase(span, pattern) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: ["Pattern match is not exhaustive"],
        hints: [
          "Add a case for the missing pattern: " <> pattern_to_string(pattern),
          "Consider using a wildcard pattern `_` to handle all remaining cases",
        ],
      )

    MatchRedundantCase(span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: ["This case is already handled by a previous pattern"],
        hints: [
          "Remove the redundant case",
          "Or use a different guard condition",
        ],
      )

    PatternMismatch(pattern, expected_ty, span1, span2) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span1),
        spans: [
          source_snippet.Highlight(
            span: to_source_span(span2),
            style: source_snippet.Secondary,
            label: Some("expected " <> type_to_string(expected_ty)),
          ),
        ],
        notes: ["Pattern has incompatible type"],
        hints: [
          "Use a pattern that matches " <> type_to_string(expected_ty),
        ],
      )

    ComptimePermissionDenied(operation, span, required) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "Operation '" <> operation <> "' requires permission",
          "Required permissions: " <> list.map(required, permission_to_string) |> string.join(", "),
        ],
        hints: [
          "Add the appropriate permission flag to your comptime block",
        ],
      )

    InfiniteType(hole_id, ty, span1, span2) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span1),
        spans: [
          source_snippet.Highlight(
            span: to_source_span(span2),
            style: source_snippet.Secondary,
            label: Some("occurs in " <> type_to_string(ty)),
          ),
        ],
        notes: [
          "Hole #" <> int.to_string(hole_id) <> " would create an infinite type",
          "This happens when a type refers to itself",
        ],
        hints: [
          "Check for recursive type definitions",
          "Use a type annotation to break the cycle",
        ],
      )

    TypeAnnotationNeeded(term) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(term.span),
        spans: [],
        notes: ["Cannot infer type for this expression"],
        hints: [
          "Add a type annotation: (term : Type)",
          "Provide more context for type inference",
        ],
      )

    RcdMissingFields(names, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: ["Missing fields: " <> string.join(names, ", ")],
        hints: [
          "Provide all required fields for this record",
        ],
      )

    CtrUnsolvedParam(tag, _ctr, id, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "Parameter for constructor `" <> tag <> "` could not be inferred",
        ],
        hints: [
          "Add a type annotation to help inference",
        ],
      )

    DotFieldNotFound(name, fields, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "Field `" <> name <> "` not found",
          "Available fields: " <> list.map(fields, fn(f) { f.0 }) |> string.join(", "),
        ],
        hints: [
          "Check the field name for typos",
        ],
      )

    DotOnNonCtr(_value, name, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "Cannot access field `" <> name <> "` on this value",
        ],
        hints: [
          "Field access only works on records",
        ],
      )

    SpineMismatch(span1, span2) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span1),
        spans: [
          source_snippet.Highlight(
            span: to_source_span(span2),
            style: source_snippet.Secondary,
            label: Some("application context"),
          ),
        ],
        notes: ["Function application has incompatible types"],
        hints: [
          "Check that the function and argument types match",
        ],
      )

    TODO(message) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: source_snippet.Span("unknown", 0, 0, 0, 1),
        spans: [],
        notes: [message],
        hints: ["This feature is not yet implemented"],
      )
  }
}

// ============================================================================
// HELPERS
// ============================================================================

fn to_source_span(span: grammar.Span) -> source_snippet.Span {
  source_snippet.Span(span.file, span.start_line, span.start_col, span.end_line, span.end_col)
}

fn type_to_string(ty: Type) -> String {
  case ty {
    VTyp(_) -> "Type"
    VLit(lit) -> literal_type_from_value(lit)
    VLitT(lit) -> literal_type_to_string(lit)
    VNeut(head, _) -> head_to_string(head)
    VRcd(_) -> "{...}"
    VCtr(tag, _) -> tag
    VLam(_, _, _) -> "λ"
    VPi(name, _, domain, _) ->
      "(" <> name <> " : " <> type_to_string(domain) <> ") → ..."
    VCall(name, _) -> name
    VFix(_, _, _) -> "fix"
    VErr -> "⊥"
  }
}

fn literal_type_to_string(lit: LiteralType) -> String {
  case lit {
    I32T -> "$I32"
    I64T -> "$I64"
    U32T -> "$U32"
    U64T -> "$U64"
    F32T -> "$F32"
    F64T -> "$F64"
  }
}

fn literal_type_from_value(lit: Literal) -> String {
  case lit {
    I32(_) -> "$I32"
    I64(_) -> "$I64"
    U32(_) -> "$U32"
    U64(_) -> "$U64"
    F32(_) -> "$F32"
    F64(_) -> "$F64"
  }
}

fn value_to_type(value: Val) -> Type {
  value
}

fn pattern_to_string(pattern: Pattern) -> String {
  case pattern {
    PAny -> "_"
    PAs(pat, name) -> name <> "@" <> pattern_to_string(pat)
    PTyp(_) -> "Type"
    PLit(lit) -> literal_to_string(lit)
    PLitT(lit) -> literal_type_to_string(lit)
    PRcd(fields) -> "{ " <> list.map(fields, fn(f) { f.0 <> " = ..." }) |> string.join(", ") <> " }"
    PCtr(tag, arg) -> tag <> "(" <> pattern_to_string(arg) <> ")"
  }
}

fn literal_to_string(lit: Literal) -> String {
  case lit {
    I32(n) -> int.to_string(n)
    I64(n) -> int.to_string(n)
    U32(n) -> int.to_string(n)
    U64(n) -> int.to_string(n)
    F32(f) -> float_to_string(f)
    F64(f) -> float_to_string(f)
  }
}

fn float_to_string(f: Float) -> String {
  // Simple float to string conversion
  case f {
    0.0 -> "0.0"
    1.0 -> "1.0"
    _ -> "float"
  }
}

fn bool_to_string(b: Bool) -> String {
  case b {
    True -> "true"
    False -> "false"
  }
}

fn head_to_string(head: Head) -> String {
  case head {
    HVar(index) -> "var[" <> int.to_string(index) <> "]"
    HHole(id) -> "hole[" <> int.to_string(id) <> "]"
  }
}

fn permission_to_string(perm: Permission) -> String {
  case perm {
    AllowRead(path) -> "Read(" <> path <> ")"
    AllowWrite(path) -> "Write(" <> path <> ")"
  }
}

fn type_mismatch_hints(expected: Type, got: Type, _source: String, _span: grammar.Span) -> List(String) {
  // Provide contextual hints based on the types involved
  let base_hints = [
    "Check that the expression has the expected type",
    "Consider adding a type annotation",
  ]

  // Add specific hints based on type combinations
  let expected_str = type_to_string(expected)
  let got_str = type_to_string(got)

  let specific_hints = case expected_str, got_str {
    "$I32", "$F64" -> ["Use `round` or `floor` to convert Float to Int"]
    "$F64", "$I32" -> ["Use `to_float` to convert Int to Float"]
    "$String", "$I32" -> ["Use `int.to_string` to convert Int to String"]
    "$I32", "$String" -> ["Use `int.parse` to convert String to Int"]
    _, _ -> []
  }

  list.append(base_hints, specific_hints)
}

// ============================================================================
// FORMATTED OUTPUT
// ============================================================================

pub fn format_error(error: Error, source: String, file: String) -> String {
  let diagnostic = error_to_diagnostic(error, source, file)
  format_diagnostic(diagnostic, source)
}

pub fn format_diagnostic(diagnostic: Diagnostic, source: String) -> String {
  let header = format_header(diagnostic)
  let snippet = format_snippet(diagnostic, source)
  let footer = format_footer(diagnostic)

  string.join([header, snippet, footer] |> list.filter(fn(s) { s != "" }), "\n")
}

fn format_header(diagnostic: Diagnostic) -> String {
  let emoji = case diagnostic.severity {
    source_snippet.Error -> emoji_error
    source_snippet.Warning -> emoji_warning
    source_snippet.Info -> emoji_info
  }

  let severity_str = case diagnostic.severity {
    source_snippet.Error -> "error"
    source_snippet.Warning -> "warning"
    source_snippet.Info -> "info"
  }

  emoji <> " " <> severity_str <> "[" <> diagnostic.code <> "]: " <> diagnostic.message
}

fn format_snippet(diagnostic: Diagnostic, source: String) -> String {
  source_snippet.format_diagnostic(diagnostic, source)
}

fn format_footer(diagnostic: Diagnostic) -> String {
  let notes = diagnostic.notes
  |> list.map(fn(note) { emoji_note <> " note: " <> note })

  let hints = diagnostic.hints
  |> list.map(fn(hint) { emoji_help <> " help: " <> hint })

  let footer_items = list.append(notes, hints)

  case footer_items {
    [] -> ""
    [..] -> "\n" <> string.join(footer_items, "\n")
  }
}
