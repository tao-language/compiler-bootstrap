// ============================================================================
// FORMATTER - Document Algebra Pretty Printer
// ============================================================================
import gleam/list
import gleam/option.{type Option}
import gleam/string

pub type Doc {
  Empty
  Text(String)
  Line
  HardLine
  Group(Doc)
  Nest(Int, Doc)
  Concat(List(Doc))
}

pub fn empty() -> Doc {
  Empty
}

pub fn text(s: String) -> Doc {
  case s == "" {
    True -> Empty
    False -> Text(s)
  }
}

pub fn line() -> Doc {
  Line
}

pub fn space() -> Doc {
  Text(" ")
}

pub fn hardline() -> Doc {
  HardLine
}

pub fn concat(docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [d] -> d
    _ -> Concat(docs)
  }
}

pub fn append(d1: Doc, d2: Doc) -> Doc {
  concat([d1, d2])
}

pub fn nest(n: Int, doc: Doc) -> Doc {
  case n <= 0 {
    True -> doc
    False -> Nest(n, doc)
  }
}

pub fn group(doc: Doc) -> Doc {
  Group(doc)
}

pub fn join(sep: Doc, docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [first] -> first
    [first, ..rest] -> {
      list.fold(over: rest, from: first, with: fn(acc, d) {
        concat([acc, sep, d])
      })
    }
  }
}

pub fn space_sep(docs: List(Doc)) -> Doc {
  join(text(" "), docs)
}

pub fn comma_sep(docs: List(Doc)) -> Doc {
  join(concat([text(","), line()]), docs)
}

pub fn parens(doc: Doc) -> Doc {
  concat([text("("), doc, text(")")])
}

pub fn braces(doc: Doc) -> Doc {
  concat([text("{"), doc, text("}")])
}

pub fn render(doc: Doc, width: Int) -> String {
  let formatted = format_to_string(doc, width, 0, True)
  string.trim(formatted)
}

pub fn render_default(doc: Doc) -> String {
  render(doc, 80)
}

fn format_to_string(doc: Doc, width: Int, indent: Int, flat: Bool) -> String {
  case doc {
    Empty -> ""
    Text(s) -> s
    Line -> {
      case flat {
        True -> " "
        False -> "\n" <> string.repeat(" ", indent)
      }
    }
    HardLine -> "\n" <> string.repeat(" ", indent)
    Group(inner) -> {
      let flat_str = format_to_string(inner, width, indent, True)
      case fits(flat_str, width) {
        True -> flat_str
        False -> format_to_string(inner, width, indent, False)
      }
    }
    Nest(n, inner) -> format_to_string(inner, width, indent + n, flat)
    Concat(docs) -> {
      string.concat(
        list.map(docs, fn(d) { format_to_string(d, width, indent, flat) }),
      )
    }
  }
}

fn fits(s: String, width: Int) -> Bool {
  case string.contains(s, "\n") {
    True -> False
    False -> {
      let lines = string.split(s, "\n")
      case lines {
        [first] -> string.length(first) <= width
        _ -> False
      }
    }
  }
}

// ============================================================================
// METADATA-AWARE FORMATTER COMBINATORS
// ============================================================================
/// Format binary operator with automatic precedence lookup.
///
/// Instead of passing precedence manually, pass a precedence value.
/// Precedence is defined in grammar and should be passed here.
///
/// Example:
/// ```gleam
/// fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
///   case ast {
///     Add(l, r) ->
///       formatter.format_binop_auto(
///         format_expr,  // Recursive formatter
///         l,
///         r,
///         " + ",  // ← Operator separator
///         10,  // ← Precedence from grammar
///         parent_prec,
///       )
///   }
/// }
/// ```
pub fn format_binop_auto(
  format_fn: fn(a, Int) -> Doc,  // Recursive formatter
  left: a,
  right: a,
  separator: String,
  prec: Int,
  parent_prec: Int,
) -> Doc {
  let left_doc = format_fn(left, prec)
  let right_doc = format_fn(right, prec + 1)
  
  let doc = concat([left_doc, text(" "), text(separator), text(" "), right_doc])
  
  case prec < parent_prec {
    True -> parens(doc)
    False -> doc
  }
}

/// Format binary operator with custom separator and layout.
///
/// Example:
/// ```gleam
/// format_binop_with_layout(
///   format_expr, l, r,
///   " + ",  // Separator
///   False,  // break_before
///   False,  // break_after
///   False,  // indent_rhs
///   10, parent_prec,
/// )
/// ```
pub fn format_binop_with_layout(
  format_fn: fn(a, Int) -> Doc,
  left: a,
  right: a,
  separator: String,
  break_before: Bool,
  break_after: Bool,
  indent_rhs: Bool,
  prec: Int,
  parent_prec: Int,
) -> Doc {
  let left_doc = format_fn(left, prec)
  let right_doc = format_fn(right, prec + 1)
  
  let separator_doc = case break_before {
    True -> concat([hardline(), text(separator)])
    False -> text(separator)
  }
  
  let right_indent = case indent_rhs {
    True -> 2
    False -> 0
  }
  
  let doc = concat([
    left_doc,
    separator_doc,
    case break_after {
      True -> line()
      False -> empty()
    },
    nest(right_indent, right_doc),
  ])
  
  case prec < parent_prec {
    True -> parens(doc)
    False -> doc
  }
}

/// Format unary operator (prefix).
///
/// Example:
/// ```gleam
/// format_unary("-", format_expr(operand, 90))
/// ```
pub fn format_unary(op: String, operand: Doc) -> Doc {
  concat([text(op), operand])
}

/// Format unary operator (postfix).
///
/// Example:
/// ```gleam
/// format_unary_postfix(format_expr(operand, 90), "!")
/// ```
pub fn format_unary_postfix(operand: Doc, op: String) -> Doc {
  concat([operand, text(op)])
}

/// Format wrapped expression (parens, braces, brackets, etc.).
///
/// Example:
/// ```gleam
/// format_wrapped("(", format_expr(inner, 0), ")")
/// format_wrapped("{", format_fields(fields), "}")
/// ```
pub fn format_wrapped(open: String, content: Doc, close: String) -> Doc {
  concat([text(open), content, text(close)])
}

/// Format list of items with separator.
///
/// Example:
/// ```gleam
/// format_list(
///   [format_expr(a, 0), format_expr(b, 0), format_expr(c, 0)],
///   text(", "),
/// )
/// ```
pub fn format_list(items: List(Doc), sep: Doc) -> Doc {
  join(sep, items)
}

/// Format function application.
///
/// Example:
/// ```gleam
/// format_application(
///   format_expr(fun, 85),
///   [format_expr(arg1, 0), format_expr(arg2, 0)],
/// )
/// ```
pub fn format_application(fun: Doc, args: List(Doc)) -> Doc {
  concat([
    fun,
    text("("),
    format_list(args, concat([text(","), line()])),
    text(")"),
  ])
}

/// Format lambda abstraction.
///
/// Example:
/// ```gleam
/// format_lambda(
///   ["x", "y"],
///   format_expr(body, 0),
/// )
/// ```
pub fn format_lambda(params: List(String), body: Doc) -> Doc {
  concat([
    text("fn("),
    format_list(params |> list.map(text), concat([text(","), line()])),
    text(") -> "),
    body,
  ])
}

/// Format record with fields.
///
/// Example:
/// ```gleam
/// format_record([
///   #("x", format_expr(x, 0)),
///   #("y", format_expr(y, 0)),
/// ])
/// ```
pub fn format_record(fields: List(#(String, Doc))) -> Doc {
  let field_docs = fields |> list.map(fn(f) {
    let #(name, value) = f
    concat([text(name), text(": "), value])
  })
  format_wrapped(
    "{ ",
    format_list(field_docs, concat([text(", "), line()])),
    " }",
  )
}

/// Format record with automatic layout (inline or multi-line).
///
/// Tries inline first, then breaks if too long.
///
/// Example:
/// ```gleam
/// format_record_auto([
///   #("x", format_expr(x, 0)),
///   #("y", format_expr(y, 0)),
/// ], 80)
/// ```
pub fn format_record_auto(
  fields: List(#(String, Doc)),
  width: Int,
) -> Doc {
  let inline = format_record_inline(fields)
  case fits(render(inline, width), width) {
    True -> inline
    False -> format_record_break(fields)
  }
}

fn format_record_inline(fields: List(#(String, Doc))) -> Doc {
  let field_docs = fields |> list.map(fn(f) {
    let #(name, value) = f
    concat([text(name), text(": "), value])
  })
  format_wrapped("{ ", format_list(field_docs, text(", ")), " }")
}

fn format_record_break(fields: List(#(String, Doc))) -> Doc {
  let field_docs = fields |> list.map(fn(f) {
    let #(name, value) = f
    concat([text("  "), text(name), text(": "), value])
  })
  format_wrapped("{\n", format_list(field_docs, text(",\n")), "\n}")
}

/// Format match expression.
///
/// Example:
/// ```gleam
/// format_match(
///   format_expr(scrutinee, 85),
///   [
///     format_case(pattern1, guard1, body1),
///     format_case(pattern2, guard2, body2),
///   ],
/// )
/// ```
pub fn format_match(scrutinee: Doc, cases: List(Doc)) -> Doc {
  concat([
    text("match "),
    scrutinee,
    text(" {"),
    hardline(),
    format_list(cases, hardline()),
    hardline(),
    text("}"),
  ])
}

/// Format single match case.
///
/// Example:
/// ```gleam
/// format_case(
///   format_pattern(pattern),
///   Some(format_expr(guard, 0)),
///   format_expr(body, 0),
/// )
/// ```
pub fn format_case(pattern: Doc, guard: Option(Doc), body: Doc) -> Doc {
  let guard_doc = case guard {
    option.Some(g) -> concat([text(" if "), g])
    option.None -> empty()
  }
  concat([
    text("| "),
    pattern,
    guard_doc,
    text(" -> "),
    body,
  ])
}

/// Format inline (no breaks).
///
/// Wraps in group to try fitting on one line.
pub fn format_inline(format_fn: fn(a) -> Doc, value: a) -> Doc {
  group(format_fn(value))
}

/// Format with soft breaks (break if needed).
pub fn format_soft_break(format_fn: fn(a) -> Doc, value: a) -> Doc {
  format_fn(value)
}

/// Format with hard breaks (always break).
pub fn format_hard_break(format_fn: fn(a) -> Doc, value: a) -> Doc {
  format_fn(value)
}
