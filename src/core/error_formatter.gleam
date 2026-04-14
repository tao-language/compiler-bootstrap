// ============================================================================
// CORE ERROR FORMATTER
// ============================================================================
/// Tao-style error messages with emoji-guided navigation and visual hierarchy.
///
/// Produces output like:
/// ```
/// ❌ error[E0101]: ast.Type mismatch
///    ┌─ src/file.core:3:5
///    │
///  3 │ (x : %ast.I32) -> x
///    │     ━━━━━ expected %ast.Type, found %ast.I32
///    │
///    💡 expected because this is %ast.Type
///    📝 note: %ast.Type and %ast.I32 are incompatible types
///    🔧 help: use a type annotation or check your term
/// ```
import core/color.{type ColorConfig, should_use_colors, default_config, colorize_error_header, colorize_warning_header, colorize_info_header, colorize_note, colorize_help, strip_ansi_codes}
import core/ast as ast
import core/state.{
  type Error, type Permission,
  SyntaxError, TypeMismatch, PatternMismatch, NotAFunction, VarUndefined, HoleUnsolved,
  ArityMismatch, CtrUndefined, MatchRedundantCase, MatchMissingCase,
  ComptimePermissionDenied, InfiniteType,
  RcdMissingFields, CtrUnsolvedParam, DotFieldNotFound, DotOnNonCtr,
  SpineMismatch, TODO, NameShadow,
  AllowRead, AllowWrite,
}
import gleam/float
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
    SyntaxError(..) -> "E0001"
    TypeMismatch(..) -> "E0101"
    VarUndefined(..) -> "E0102"
    NotAFunction(..) -> "E0103"
    ArityMismatch(..) -> "E0104"
    CtrUndefined(..) -> "E0105"
    HoleUnsolved(..) -> "E0106"
    InfiniteType(..) -> "E0107"
    RcdMissingFields(..) -> "E0108"
    CtrUnsolvedParam(..) -> "E0109"
    DotFieldNotFound(..) -> "E0110"
    DotOnNonCtr(..) -> "E0111"
    SpineMismatch(..) -> "E0112"
    PatternMismatch(..) -> "E0201"
    MatchMissingCase(..) -> "E0202"
    MatchRedundantCase(..) -> "E0203"
    ComptimePermissionDenied(..) -> "E0501"
    NameShadow(..) -> "E0301"
    TODO(..) -> "E9999"
  }
}

pub fn error_message(error: Error) -> String {
  case error {
    SyntaxError(..) -> "Syntax error"
    TypeMismatch(..) -> "ast.Type mismatch"
    VarUndefined(..) -> "Undefined variable"
    NotAFunction(..) -> "Cannot call non-function value"
    ArityMismatch(..) -> "Wrong number of arguments"
    CtrUndefined(..) -> "Constructor not found"
    HoleUnsolved(..) -> "Unsolved hole"
    InfiniteType(..) -> "Infinite type"
    RcdMissingFields(..) -> "Missing record fields"
    CtrUnsolvedParam(..) -> "Constructor parameter unsolved"
    DotFieldNotFound(..) -> "Field not found"
    DotOnNonCtr(..) -> "Cannot access field on non-record"
    SpineMismatch(..) -> "Function application mismatch"
    PatternMismatch(..) -> "ast.Pattern type mismatch"
    MatchMissingCase(..) -> "ast.Pattern match not exhaustive"
    MatchRedundantCase(..) -> "Redundant pattern"
    ComptimePermissionDenied(..) -> "Permission denied"
    NameShadow(..) -> "Duplicate definition"
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
    SyntaxError(span, expected, got, context) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message <> case context {
          "" -> ""
          _ -> " in " <> context
        },
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "Expected: " <> expected,
          "Got: " <> got,
        ],
        hints: [
          "Check for typos or missing tokens",
          "Ensure expressions are well-formed",
          "Review the syntax documentation",
        ],
      )

    TypeMismatch(expected, got, expected_span, got_span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(expected_span),
        spans: [
          source_snippet.Highlight(
            span: to_source_span(got_span),
            style: source_snippet.Secondary,
            label: Some("expected " <> type_to_string(expected) <> ", found " <> type_to_string(got)),
          ),
        ],
        notes: [
          type_to_string(expected) <> " and " <> type_to_string(got) <> " are incompatible types",
          "The expression produces " <> type_to_string(got) <> " but " <> type_to_string(expected) <> " is expected here",
        ],
        hints: type_mismatch_hints(expected, got, source, expected_span),
      )

    VarUndefined(index, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "Variable at index " <> int.to_string(index) <> " is not defined in this scope",
          "Variables must be defined before they are used, typically in a let binding or lambda parameter",
        ],
        hints: [
          "Check variable name and scope",
          "Did you forget to define this variable?",
          "Check for typos in the variable name",
        ],
      )

    NotAFunction(fun, fun_ty) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(ast.get_span(fun)),
        spans: [],
        notes: [
          "This value has type " <> type_to_string(fun_ty) <> ", which is not callable",
          "Only function values (created with ->) can be called with parentheses",
        ],
        hints: [
          "Only functions can be called with parentheses",
          "Check that you're calling a function, not a value",
          "If you want a function, use a lambda: x -> expression",
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
        notes: [
          "Expected a different number of arguments",
          "Functions in this language are curried - each parameter needs its own arrow",
        ],
        hints: [
          "Check the function signature and provide the correct number of arguments",
          "Remember: f(x, y) applies f to a tuple, while f(x)(y) is curried application",
          "Use a type annotation to clarify the expected arity",
        ],
      )

    CtrUndefined(tag, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "Constructor `" <> tag <> "` is not defined in the current scope",
          "Constructors must be defined before use, typically in a data type declaration",
        ],
        hints: [
          "Check the constructor name for typos",
          "Make sure the constructor is defined in the current scope",
          "Define a type with this constructor first",
        ],
      )

    HoleUnsolved(id, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "Hole #" <> int.to_string(id) <> " was not solved during type checking",
          "Holes are development placeholders that must be replaced before the program is complete",
        ],
        hints: [
          "Holes are placeholders that must be filled",
          "Provide a term of the expected type",
          "Use holes temporarily during development, then replace them",
        ],
      )

    MatchMissingCase(span, pattern) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "ast.Pattern match is not exhaustive",
          "Missing case for: " <> pattern_to_string(pattern),
        ],
        hints: [
          "Add a case for the missing pattern: | " <> pattern_to_string(pattern) <> " -> ...",
          "Consider using a wildcard pattern `_` to handle all remaining cases",
          "Ensure all constructors are covered for complete safety",
        ],
      )

    MatchRedundantCase(span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "This case is already handled by a previous pattern",
          "Redundant cases indicate dead code that will never execute",
        ],
        hints: [
          "Remove the redundant case",
          "Or use a different guard condition",
          "Reorder cases to put specific patterns before wildcards",
        ],
      )

    PatternMismatch(_pattern, expected_type, pattern_span, value_span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(pattern_span),
        spans: [
          source_snippet.Highlight(
            span: to_source_span(value_span),
            style: source_snippet.Secondary,
            label: Some("expected " <> type_to_string(expected_type)),
          ),
        ],
        notes: [
          "ast.Pattern has incompatible type",
          "The pattern expects " <> type_to_string(expected_type) <> " but the matched value has a different type",
        ],
        hints: [
          "Use a pattern that matches " <> type_to_string(expected_type),
          "Check the type of the value being matched",
          "Consider adding a type annotation to clarify expectations",
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
          "Move the operation to runtime (outside comptime)",
          "Review comptime permission requirements in the documentation",
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
          "Infinite types like T = T -> ? are not allowed",
        ],
        hints: [
          "Check for recursive type definitions",
          "Add a type annotation to break the cycle",
          "Consider using a fixpoint combinator instead",
        ],
      )

    RcdMissingFields(names, span) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(span),
        spans: [],
        notes: [
          "Missing fields: " <> string.join(names, ", "),
          "Records must include all defined fields",
        ],
        hints: [
          "Provide all required fields for this record",
          "Check the record definition for the complete field list",
          "Add the missing fields with appropriate values",
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
          "Hole #" <> int.to_string(id) <> " remains unsolved",
        ],
        hints: [
          "Add a type annotation to help inference",
          "Provide more context for the constructor application",
          "Check that the constructor is fully applied",
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
          "Use one of the available fields listed above",
          "Add the field to the record definition if needed",
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
          "Field access (.field) only works on records",
        ],
        hints: [
          "Use a record value instead of a primitive",
          "Check that you're accessing a record, not a number or other type",
          "Wrap the value in a record: {value: x}.field",
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
        notes: [
          "Function application has incompatible types",
          "The function's expected arguments don't match the provided arguments",
        ],
        hints: [
          "Check that the function and argument types match",
          "Review the function's type signature",
          "Add type annotations to clarify expectations",
        ],
      )

    NameShadow(name, first_def, second_def) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: to_source_span(second_def),
        spans: [
          source_snippet.Highlight(
            span: to_source_span(first_def),
            style: source_snippet.Secondary,
            label: Some("First defined here"),
          ),
        ],
        notes: [
          "`" <> name <> "` was already defined at the module level",
          "Shadowing is not allowed for top-level definitions",
        ],
        hints: [
          "Use a different name for this definition",
          "Remove the previous definition if no longer needed",
          "Within functions, shadowing is allowed",
        ],
      )

    TODO(message) ->
      source_snippet.Diagnostic(
        code: code,
        severity: severity,
        message: message,
        primary_span: source_snippet.Span("unknown", 0, 0, 0, 1),
        spans: [],
        notes: [
          message,
          "This is a placeholder for incomplete code",
        ],
        hints: [
          "This feature is not yet implemented",
          "Implement the missing functionality",
          "Replace TODO with actual implementation",
        ],
      )
  }
}

// ============================================================================
// HELPERS
// ============================================================================

fn to_source_span(span: grammar.Span) -> source_snippet.Span {
  source_snippet.Span(span.file, span.start_line, span.start_col, span.end_line, span.end_col)
}

fn type_to_string(ty: ast.Type) -> String {
  case ty {
    ast.VTyp(_) -> "ast.Type"
    ast.VLit(lit) -> literal_type_from_value(lit)
    ast.VLitT(lit) -> literal_type_to_string(lit)
    ast.VNeut(head, _) -> head_to_string(head)
    ast.VRcd(_) -> "{...}"
    ast.VCtrValue(ctr) -> ctr_to_string(ctr)
    ast.VLam(_, _, _, _) -> "λ"
    ast.VPi(_, _, _, domain, _) ->
      "(" <> type_to_string(domain) <> ") → ..."
    ast.VRcd(_) -> "{...}"
    ast.VRecord(_) -> "Record{...}"
    ast.VCall(name, _) -> name
    ast.VFix(_, _, _) -> "fix"
    ast.VUnit -> "Unit"
    ast.VErr -> "⊥"
  }
}

fn ctr_to_string(ctr) -> String {
  case ctr {
    ast.VCtr(tag, ast.VUnit) -> tag
    ast.VCtr(tag, arg) -> "#" <> tag <> "(" <> value_to_string(arg) <> ")"
  }
}

fn value_to_string(val: ast.Value) -> String {
  case val {
    ast.VUnit -> "Unit"
    ast.VTyp(_) -> "Type"
    ast.VLit(lit) -> literal_from_value(lit)
    ast.VLitT(lit) -> literal_type_to_string(lit)
    ast.VNeut(head, _) -> head_to_string(head)
    ast.VRcd(_) -> "{...}"
    ast.VCtrValue(ctr) -> ctr_to_string(ctr)
    ast.VLam(_, _, _, _) -> "λ"
    ast.VPi(_, _, _, domain, _) -> "(" <> type_to_string(domain) <> ") → ..."
    ast.VRecord(_) -> "Record{...}"
    ast.VCall(name, _) -> name <> "(...)"
    ast.VFix(_, _, _) -> "fix"
    ast.VUnit -> "Unit"
    ast.VErr -> "⊥"
  }
}

fn literal_from_value(lit: ast.Literal) -> String {
  case lit {
    ast.I32(n) -> int.to_string(n)
    ast.I64(n) -> int.to_string(n)
    ast.U32(n) -> int.to_string(n)
    ast.U64(n) -> int.to_string(n)
    ast.F32(f) -> "" <> float.to_string(f)
    ast.F64(f) -> "" <> float.to_string(f)
    ast.IntLit(n) -> int.to_string(n)
    ast.FloatLit(f) -> "" <> float.to_string(f)
  }
}

fn literal_type_to_string(lit: ast.LiteralType) -> String {
  case lit {
    ast.I32T -> "Int"
    ast.I64T -> "Int"
    ast.U32T -> "Int"
    ast.U64T -> "Int"
    ast.F32T -> "Float"
    ast.F64T -> "Float"
    ast.ILitT -> "Int (any integer type)"
    ast.FLitT -> "Float (any float type)"
  }
}

fn literal_type_from_value(lit: ast.Literal) -> String {
  case lit {
    ast.I32(_) -> "Int"
    ast.I64(_) -> "Int"
    ast.U32(_) -> "Int"
    ast.U64(_) -> "Int"
    ast.F32(_) -> "Float"
    ast.F64(_) -> "Float"
    ast.IntLit(_) -> "Int (any integer type)"
    ast.FloatLit(_) -> "Float (any float type)"
  }
}

fn value_to_type(value: ast.Value) -> ast.Type {
  value
}

fn pattern_to_string(pattern: ast.Pattern) -> String {
  case pattern {
    ast.PAny -> "_"
    ast.PAs(pat, name) -> name <> "@" <> pattern_to_string(pat)
    ast.PTyp(_) -> "ast.Type"
    ast.PLit(lit) -> literal_to_string(lit)
    ast.PLitT(lit) -> literal_type_to_string(lit)
    ast.PRcd(fields) -> "{ " <> list.map(fields, fn(f) { f.0 <> " = ..." }) |> string.join(", ") <> " }"
    ast.PCtr(tag, arg) -> tag <> "(" <> pattern_to_string(arg) <> ")"
    ast.PUnit -> "Unit"
  }
}

fn literal_to_string(lit: ast.Literal) -> String {
  case lit {
    ast.I32(n) -> int.to_string(n)
    ast.I64(n) -> int.to_string(n)
    ast.U32(n) -> int.to_string(n)
    ast.U64(n) -> int.to_string(n)
    ast.F32(f) -> float_to_string(f)
    ast.F64(f) -> float_to_string(f)
    ast.IntLit(n) -> int.to_string(n)
    ast.FloatLit(f) -> float_to_string(f)
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

fn head_to_string(head: ast.Head) -> String {
  case head {
    ast.HVar(index) -> "var[" <> int.to_string(index) <> "]"
    ast.HHole(id) -> "hole[" <> int.to_string(id) <> "]"
    ast.HStepLimit -> "<step-limit>"
  }
}

fn permission_to_string(perm: Permission) -> String {
  case perm {
    AllowRead(path) -> "Read(" <> path <> ")"
    AllowWrite(path) -> "Write(" <> path <> ")"
  }
}

fn type_mismatch_hints(expected: ast.Type, got: ast.Type, _source: String, _span: grammar.Span) -> List(String) {
  // Provide contextual hints based on the types involved
  let base_hints = [
    "Check that the expression has the expected type",
    "Consider adding a type annotation",
  ]

  // Add specific hints based on type combinations
  let expected_str = type_to_string(expected)
  let got_str = type_to_string(got)

  let specific_hints = case expected_str, got_str {
    "$ast.I32", "$ast.F64" -> ["Use `round` or `floor` to convert Float to Int"]
    "$ast.F64", "$ast.I32" -> ["Use `to_float` to convert Int to Float"]
    "$String", "$ast.I32" -> ["Use `int.to_string` to convert Int to String"]
    "$ast.I32", "$String" -> ["Use `int.parse` to convert String to Int"]
    _, _ -> []
  }

  list.append(base_hints, specific_hints)
}

// ============================================================================
// FORMATTED OUTPUT
// ============================================================================

/// Format an error with default color configuration
pub fn format_error(error: Error, source: String, file: String) -> String {
  format_error_with_config(error, source, file, default_config)
}

/// Format an error with custom color configuration
pub fn format_error_with_config(
  error: Error,
  source: String,
  file: String,
  color_config: ColorConfig,
) -> String {
  let diagnostic = error_to_diagnostic(error, source, file)
  format_diagnostic_with_config(diagnostic, source, color_config)
}

/// Format a diagnostic with default color configuration
pub fn format_diagnostic(diagnostic: Diagnostic, source: String) -> String {
  format_diagnostic_with_config(diagnostic, source, default_config)
}

/// Format a diagnostic with custom color configuration
pub fn format_diagnostic_with_config(
  diagnostic: Diagnostic,
  source: String,
  color_config: ColorConfig,
) -> String {
  let header = format_header_with_config(diagnostic, color_config)
  let snippet = format_snippet_with_config(diagnostic, source, color_config)
  let footer = format_footer_with_config(diagnostic, color_config)

  string.join([header, snippet, footer] |> list.filter(fn(s) { s != "" }), "\n")
}

fn format_header_with_config(diagnostic: Diagnostic, config: ColorConfig) -> String {
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

  let header_text = emoji <> " " <> severity_str <> "[" <> diagnostic.code <> "]: " <> diagnostic.message

  case diagnostic.severity {
    source_snippet.Error -> colorize_error_header(header_text, config)
    source_snippet.Warning -> colorize_warning_header(header_text, config)
    source_snippet.Info -> colorize_info_header(header_text, config)
  }
}

fn format_snippet_with_config(
  diagnostic: Diagnostic,
  source: String,
  config: ColorConfig,
) -> String {
  // Use the source_snippet formatter, then optionally colorize it
  let snippet = source_snippet.format_diagnostic(diagnostic, source)

  // For now, just return the snippet as-is
  // Future: could add color to the snippet itself
  case should_use_colors(config) {
    True -> snippet  // source_snippet may add its own colors
    False -> strip_ansi_codes(snippet)
  }
}

fn format_footer_with_config(diagnostic: Diagnostic, config: ColorConfig) -> String {
  let notes = diagnostic.notes
  |> list.map(fn(note) {
    let text = emoji_note <> " note: " <> note
    colorize_note(text, config)
  })

  let hints = diagnostic.hints
  |> list.map(fn(hint) {
    let text = emoji_help <> " help: " <> hint
    colorize_help(text, config)
  })

  let footer_items = list.append(notes, hints)

  case footer_items {
    [] -> ""
    _ -> "\n" <> string.join(footer_items, "\n")
  }
}
