// ============================================================================
// CORE LANGUAGE FORMATTER
// ============================================================================
/// Formats core language Term AST back to source code.
/// Uses the syntax/formatter library for document algebra and layout.
///
/// # Example
///
/// ```gleam
/// import core/formatter
/// import core/core.{Term, Var, Lit, App, Lam}
/// import core/core.{I32}
///
/// let term = App(Lam("x", Var(0)), Lit(I32(42)))
/// let source = formatter.format(term)
/// // source = "(λx. x)(42)"
/// ```
import core/core.{
  type Case, type Pattern, type Term, type TermData, Ann, App, Call, Case,
  Comptime, Ctr, Dot, F32, F32T, F64, F64T, Hole, I32, I32T, I64, I64T, Lam, Lit,
  LitT, Match, PAny, PAs, PCtr, PLit, PLitT, PRcd, PTyp, Pi, Rcd, Typ, U32, U32T,
  U64, U64T, Var,
}
import gleam/float
import gleam/int
import gleam/list
import gleam/string
import syntax/formatter

// ============================================================================
// PUBLIC API
// ============================================================================

/// Format a term to source code with default width (80 chars)
pub fn format(term: Term) -> String {
  format_term(term, -1) |> formatter.render_default
}

/// Format a term to source code with specified width
pub fn format_with_width(term: Term, width: Int) -> String {
  format_term(term, -1) |> formatter.render(width)
}

// ============================================================================
// TERM FORMATTER
// ============================================================================

/// Format a term with precedence for parenthesization
fn format_term(term: Term, parent_prec: Int) -> formatter.Doc {
  case term.data {
    // Atoms (highest precedence, no parens needed)
    Typ(k) -> format_typ(k)
    Lit(value) -> format_lit(value)
    LitT(typ) -> format_lit_type(typ)
    Var(index) -> format_var(index)
    Hole(id) -> format_hole(id)
    Ctr(tag, arg) -> format_ctr(tag, arg, parent_prec)

    // Applications and field access
    Dot(arg, field) -> format_dot(arg, field, parent_prec)
    App(fun, arg) -> format_app(fun, arg, parent_prec)

    // Records
    Rcd(fields) -> format_rcd(fields, parent_prec)

    // Lambda and Pi types
    Lam(name, body) -> format_lam(name, body, parent_prec)
    Pi(name, in_, out) -> format_pi(name, in_, out, parent_prec)

    // Annotations
    Ann(term, typ) -> format_ann(term, typ, parent_prec)

    // Match expressions
    Match(arg, motive, cases) -> format_match(arg, motive, cases, parent_prec)

    // Built-in calls
    Call(name, args) -> format_call(name, args, parent_prec)

    // Comptime
    Comptime(term) -> format_comptime(term, parent_prec)
  }
}

// ============================================================================
// ATOM FORMATTERS
// ============================================================================

fn format_typ(k: Int) -> formatter.Doc {
  formatter.concat([
    formatter.text("Type"),
    formatter.text(int.to_string(k)),
  ])
}

fn format_lit(value) -> formatter.Doc {
  case value {
    I32(n) -> formatter.text(int.to_string(n))
    I64(n) ->
      formatter.concat([formatter.text(int.to_string(n)), formatter.text("i64")])
    U32(n) ->
      formatter.concat([formatter.text(int.to_string(n)), formatter.text("u32")])
    U64(n) ->
      formatter.concat([formatter.text(int.to_string(n)), formatter.text("u64")])
    F32(f) ->
      formatter.concat([
        formatter.text(float.to_string(f)),
        formatter.text("f32"),
      ])
    F64(f) -> formatter.text(float.to_string(f))
  }
}

fn format_lit_type(typ) -> formatter.Doc {
  case typ {
    I32T -> formatter.text("I32")
    I64T -> formatter.text("I64")
    U32T -> formatter.text("U32")
    U64T -> formatter.text("U64")
    F32T -> formatter.text("F32")
    F64T -> formatter.text("F64")
  }
}

fn format_var(index: Int) -> formatter.Doc {
  // For now, just show the index
  // Proper implementation would look up variable names from context
  formatter.text("var" <> int.to_string(index))
}

fn format_hole(id: Int) -> formatter.Doc {
  case id == 0 {
    True -> formatter.text("?")
    False ->
      formatter.concat([formatter.text("?"), formatter.text(int.to_string(id))])
  }
}

// ============================================================================
// APPLICATION AND FIELD ACCESS
// ============================================================================

fn format_app(fun: Term, arg: Term, parent_prec: Int) -> formatter.Doc {
  // Application precedence: 85
  let app_prec = 85

  let fun_doc = format_term(fun, app_prec)
  let arg_doc = format_term(arg, app_prec)

  let inner =
    formatter.concat([
      fun_doc,
      formatter.text("("),
      arg_doc,
      formatter.text(")"),
    ])

  wrap_parens(inner, app_prec < parent_prec)
}

fn format_dot(arg: Term, field: String, parent_prec: Int) -> formatter.Doc {
  // Field access precedence: 95
  let dot_prec = 95

  let arg_doc = format_term(arg, dot_prec)

  let inner =
    formatter.concat([
      arg_doc,
      formatter.text("."),
      formatter.text(field),
    ])

  wrap_parens(inner, dot_prec < parent_prec)
}

// ============================================================================
// CONSTRUCTORS
// ============================================================================

fn format_ctr(tag: String, arg: Term, parent_prec: Int) -> formatter.Doc {
  // Constructor application precedence: 90
  let ctr_prec = 90

  let arg_doc = format_term(arg, ctr_prec)

  let inner =
    formatter.concat([
      formatter.text(tag),
      formatter.text("("),
      arg_doc,
      formatter.text(")"),
    ])

  wrap_parens(inner, ctr_prec < parent_prec)
}

// ============================================================================
// RECORDS
// ============================================================================

fn format_rcd(fields: List(#(String, Term)), parent_prec: Int) -> formatter.Doc {
  // Record precedence: 100 (atom)
  let rcd_prec = 100

  case fields {
    [] -> formatter.text("{}")
    _ -> {
      let field_docs =
        list.map(fields, fn(field) {
          let #(name, value) = field
          formatter.concat([
            formatter.text(name),
            formatter.text(": "),
            format_term(value, rcd_prec),
          ])
        })

      let inner =
        formatter.concat([
          formatter.text("{"),
          formatter.nest(
            2,
            formatter.concat([
              formatter.line(),
              formatter.join(
                formatter.concat([formatter.text(", "), formatter.line()]),
                field_docs,
              ),
            ]),
          ),
          formatter.line(),
          formatter.text("}"),
        ])

      formatter.group(inner)
    }
  }
}

// ============================================================================
// LAMBDA AND PI TYPES
// ============================================================================

fn format_lam(name: String, body: Term, parent_prec: Int) -> formatter.Doc {
  // Lambda precedence: 70
  let lam_prec = 70

  let body_doc = format_term(body, lam_prec)

  let inner =
    formatter.concat([
      formatter.text("λ"),
      formatter.text(name),
      formatter.text(". "),
      body_doc,
    ])

  wrap_parens(inner, lam_prec < parent_prec)
}

fn format_pi(
  name: String,
  in_: Term,
  out: Term,
  parent_prec: Int,
) -> formatter.Doc {
  // Pi type precedence: 65
  let pi_prec = 65

  let in_doc = format_term(in_, pi_prec)
  let out_doc = format_term(out, pi_prec)

  let inner =
    formatter.concat([
      formatter.text("("),
      formatter.text(name),
      formatter.text(": "),
      in_doc,
      formatter.text(") → "),
      out_doc,
    ])

  wrap_parens(inner, pi_prec < parent_prec)
}

// ============================================================================
// TYPE ANNOTATIONS
// ============================================================================

fn format_ann(term: Term, typ: Term, parent_prec: Int) -> formatter.Doc {
  // Annotation precedence: 75
  let ann_prec = 75

  let term_doc = format_term(term, ann_prec)
  let typ_doc = format_term(typ, ann_prec)

  let inner =
    formatter.concat([
      term_doc,
      formatter.text(": "),
      typ_doc,
    ])

  wrap_parens(inner, ann_prec < parent_prec)
}

// ============================================================================
// MATCH EXPRESSIONS
// ============================================================================

fn format_match(
  arg: Term,
  motive: Term,
  cases: List(Case),
  parent_prec: Int,
) -> formatter.Doc {
  // Match precedence: 60
  let match_prec = 60

  let arg_doc = format_term(arg, match_prec)

  let case_docs = list.map(cases, fn(c) { format_case(c, match_prec) })

  let inner =
    formatter.concat([
      formatter.text("match "),
      arg_doc,
      formatter.text(" {"),
      formatter.nest(
        2,
        formatter.concat([
          formatter.hardline(),
          formatter.join(
            formatter.concat([formatter.text(", "), formatter.hardline()]),
            case_docs,
          ),
        ]),
      ),
      formatter.hardline(),
      formatter.text("}"),
    ])

  formatter.group(inner)
}

fn format_case(case_, _parent_prec: Int) -> formatter.Doc {
  let Case(pattern, body, _) = case_
  let pattern_doc = format_pattern(pattern)
  let body_doc = format_term(body, 60)

  formatter.concat([
    pattern_doc,
    formatter.text(" → "),
    body_doc,
  ])
}

fn format_pattern(pattern) -> formatter.Doc {
  case pattern {
    PAny -> formatter.text("_")
    PAs(p, name) ->
      formatter.concat([
        format_pattern(p),
        formatter.text(" @ "),
        formatter.text(name),
      ])
    PTyp(k) ->
      formatter.concat([
        formatter.text("Type"),
        formatter.text(int.to_string(k)),
      ])
    PLit(value) -> format_lit(value)
    PLitT(typ) -> format_lit_type(typ)
    PRcd(fields) -> format_pattern_rcd(fields)
    PCtr(tag, arg) ->
      formatter.concat([
        formatter.text(tag),
        formatter.text("("),
        format_pattern(arg),
        formatter.text(")"),
      ])
  }
}

fn format_pattern_rcd(fields: List(#(String, Pattern))) -> formatter.Doc {
  case fields {
    [] -> formatter.text("{}")
    _ -> {
      let field_docs =
        list.map(fields, fn(field) {
          let #(name, pattern) = field
          formatter.concat([
            formatter.text(name),
            formatter.text(": "),
            format_pattern(pattern),
          ])
        })

      formatter.concat([
        formatter.text("{"),
        formatter.join(formatter.text(", "), field_docs),
        formatter.text("}"),
      ])
    }
  }
}

// ============================================================================
// BUILTIN CALLS
// ============================================================================

fn format_call(
  name: String,
  args: List(Term),
  parent_prec: Int,
) -> formatter.Doc {
  // Call precedence: 85 (same as application)
  let call_prec = 85

  let arg_docs = list.map(args, fn(arg) { format_term(arg, call_prec) })

  let inner =
    formatter.concat([
      formatter.text(name),
      formatter.text("("),
      formatter.join(formatter.text(", "), arg_docs),
      formatter.text(")"),
    ])

  wrap_parens(inner, call_prec < parent_prec)
}

// ============================================================================
// COMPTIME
// ============================================================================

fn format_comptime(term: Term, parent_prec: Int) -> formatter.Doc {
  // Comptime precedence: 100 (atom-like)
  let comptime_prec = 100

  let term_doc = format_term(term, comptime_prec)

  let inner =
    formatter.concat([
      formatter.text("comptime "),
      term_doc,
    ])

  wrap_parens(inner, comptime_prec < parent_prec)
}

// ============================================================================
// HELPERS
// ============================================================================

fn wrap_parens(doc: formatter.Doc, condition: Bool) -> formatter.Doc {
  case condition {
    True -> formatter.parens(doc)
    False -> doc
  }
}
