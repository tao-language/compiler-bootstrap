import core/ast.{
  type Case, type Expr, type Pattern, type Type, type TypeDefinition,
  type Variant, PAlias, PAny, PCtr, PErr, PLit, PLitT, PRcd, PTyp,
}
import core/ffi.{type FFI}
import core/literals.{type LiteralType} as l
import core/quote.{quote}
import core/term.{type Term} as tm
import core/value.{type Value}
import glam/doc.{type Document}
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/regexp
import gleam/string

pub fn expr(e: Expr, width: Int, indent: Int) -> String {
  doc_term(e, indent)
  |> doc.to_string(width)
}

pub fn term(names: List(String), t: Term, width: Int, indent: Int) -> String {
  tm.lift(t, names)
  |> expr(width, indent)
}

pub fn value(
  ffi: FFI,
  names: List(String),
  val: Value,
  width: Int,
  indent: Int,
) -> String {
  quote(ffi, list.length(names), val)
  |> term(names, _, width, indent)
}

fn doc_text(text: String) -> Document {
  doc.from_string(text)
}

fn var_name(name: String) -> String {
  let assert Ok(var_re) = regexp.from_string("^[_a-zA-Z][_\\w]*$")
  case regexp.check(var_re, name) {
    True -> name
    False -> "`" <> string.replace(name, "`", "\\`") <> "`"
  }
}

fn doc_term(term: Expr, indent: Int) -> Document {
  case term.data {
    // Syntax sugar
    // %let name: opt_type = value; body
    ast.App(_, ast.Expr(ast.Lam(_, #(name, opt_type), body), _), value) ->
      doc.concat([
        doc_text("%let "),
        doc_text(var_name(name)),
        doc_opt_type(opt_type, indent),
        doc_text(" = "),
        doc_term(value, indent),
        doc.line,
        doc_term(body, indent),
      ])
    // Base cases
    ast.Typ(u) ->
      case u {
        0 -> doc_text("%Type")
        n -> doc_text("%Type<" <> int.to_string(n) <> ">")
      }
    ast.Hole(None) -> doc_text("?")
    ast.Hole(Some(id)) -> doc_text("?<" <> int.to_string(id) <> ">")
    ast.Lit(l) ->
      case l {
        l.Int(value) -> doc_text(int.to_string(value))
        l.Float(value) -> doc_text(float.to_string(value))
      }
    ast.LitT(t_) -> format_lit_type(t_)
    ast.Var(name) -> doc_text(var_name(name))
    ast.Ctr(tag, ast.Expr(ast.Rcd([]), _)) -> doc_text("#" <> tag)
    ast.Ctr(tag, arg) ->
      doc.concat([
        doc_text("#" <> tag <> "("),
        doc_term(arg, indent),
        doc_text(")"),
      ])
    ast.Rcd(fields) -> doc_rcd(fields, indent)
    ast.RcdT(fields) -> doc_rcdt(fields, indent)
    ast.Ann(term, type_) ->
      doc.concat([
        doc_text("%("),
        doc_term(term, indent),
        doc_text(": "),
        doc_term(type_, indent),
        doc_text(")"),
      ])
    ast.Lam(implicit, #(name, opt_type), body) -> {
      doc.concat([
        doc_text("%lam"),
        doc_param(implicit, name, opt_type, indent),
        doc_text(" => "),
        doc_term(body, indent),
      ])
    }
    ast.Pi(implicit, #(name, opt_type), body) -> {
      doc.concat([
        doc_text("%pi"),
        doc_param(implicit, name, opt_type, indent),
        doc_text(" -> "),
        doc_term(body, indent),
      ])
    }
    ast.Fix(name, body) ->
      doc.concat([
        doc_text("%fix "),
        doc_text(name),
        doc_text(". "),
        doc_term(body, indent),
      ])
    ast.App(implicit, fun, arg) -> {
      let fun_doc = doc_term(fun, indent)
      let arg_doc = doc_term(arg, indent)
      case implicit {
        True -> doc.concat([fun_doc, doc_text("<"), arg_doc, doc_text(">")])
        False -> doc.concat([fun_doc, doc_text("("), arg_doc, doc_text(")")])
      }
    }
    ast.TypeDef(type_def) -> format_typedef(type_def, indent)
    ast.Match(arg, cases) -> {
      let case_docs = list.map(cases, fn(c) { format_case(c, indent) })
      doc.concat([
        doc_text("%match "),
        doc_term(arg, indent),
        doc_text(" {"),
        doc.concat(case_docs),
        doc.line,
        doc_text("}"),
      ])
      |> doc.group
    }
    ast.Call(name, returns, args) -> {
      let arg_docs = list.map(args, doc_term(_, indent))
      doc.concat([
        doc_text("@"),
        doc_text(name),
        doc_text("<"),
        doc_term(returns, indent),
        doc_text(">"),
        doc_text("("),
        doc.join(arg_docs, doc_text(", ")),
        doc_text(")"),
      ])
    }
    ast.Err -> doc_text("%error")
  }
}

fn doc_opt_type(opt_type: Option(Type), indent: Int) -> Document {
  case opt_type {
    Some(type_) -> doc.concat([doc_text(": "), doc_term(type_, indent)])
    None -> doc.empty
  }
}

fn doc_param(
  implicit: Bool,
  name: String,
  opt_type: Option(Type),
  indent: Int,
) -> Document {
  let #(open, close) = case implicit {
    True -> #("<", ">")
    False -> #("(", ")")
  }
  doc.concat([
    doc_text(open),
    doc_text(name),
    doc_opt_type(opt_type, indent),
    doc_text(close),
  ])
}

fn doc_rcd(fields: List(#(String, Expr)), indent: Int) -> Document {
  let doc_fields =
    list.map(fields, fn(field) {
      let #(name, term) = field
      let name = var_name(name)
      doc.concat([doc_text(name <> ": "), doc_term(term, indent)])
    })
  doc.concat([
    doc_text("{"),
    doc.nest(doc.join(doc_fields, doc.break(", ", ",")), indent),
    doc_text("}"),
  ])
}

fn doc_rcdt(
  fields: List(#(String, #(Option(Expr), Option(Expr)))),
  indent: Int,
) -> Document {
  let format_field = fn(f: #(String, #(Option(Expr), Option(Expr)))) {
    let type_doc = case f.1.0 {
      Some(t) -> doc_term(t, indent)
      None -> doc_text("?")
    }
    let field_str = doc.concat([doc_text(f.0 <> ": "), type_doc])
    case f.1.1 {
      Some(default_) ->
        doc.concat([field_str, doc_text(" = "), doc_term(default_, indent)])
      None -> field_str
    }
  }
  case fields {
    [] -> doc_text("%{}")
    [field] -> doc.concat([doc_text("%{"), format_field(field), doc_text("}")])
    _ -> {
      let field_docs = list.map(fields, format_field)
      doc.concat([
        doc_text("%{"),
        doc.nest(
          doc.concat([
            doc.line,
            doc.join(field_docs, doc.concat([doc_text(","), doc.line])),
          ]),
          2,
        ),
        doc.line,
        doc_text("}"),
      ])
      |> doc.group
    }
  }
}

fn format_lit_type(lt: LiteralType) -> Document {
  case lt {
    _ if lt == l.IntT -> doc_text("%Int")
    _ if lt == l.FloatT -> doc_text("%Float")
    _ if lt == l.I8 -> doc_text("%I8")
    _ if lt == l.I16 -> doc_text("%I16")
    _ if lt == l.I32 -> doc_text("%I32")
    _ if lt == l.I64 -> doc_text("%I64")
    _ if lt == l.U8 -> doc_text("%U8")
    _ if lt == l.U16 -> doc_text("%U16")
    _ if lt == l.U32 -> doc_text("%U32")
    _ if lt == l.U64 -> doc_text("%U64")
    _ if lt == l.F16 -> doc_text("%F16")
    _ if lt == l.F32 -> doc_text("%F32")
    _ -> doc_text("%F64")
  }
}

fn format_case(c: Case, indent: Int) -> Document {
  doc.concat([
    doc.line,
    doc_text("| "),
    doc_pattern(c.pattern, indent),
    doc_case_guard(c.guard, indent),
    doc_text(" => "),
    doc.nest(doc_term(c.body, indent), indent),
  ])
}

fn doc_case_guard(guard: Option(#(Expr, Pattern)), indent: Int) -> Document {
  case guard {
    Some(#(term, pattern)) ->
      doc.concat([
        doc_text(" ? "),
        doc_term(term, indent),
        doc_text(" ~ "),
        doc_pattern(pattern, indent),
      ])
    None -> doc.empty
  }
}

fn doc_pattern(pattern: Pattern, indent: Int) -> Document {
  case pattern.data {
    PAny -> doc_text("_")
    PTyp(u) ->
      case u {
        0 -> doc_text("%Type")
        n -> doc_text("%Type<" <> int.to_string(n) <> ">")
      }
    PLit(l) ->
      case l {
        l.Int(n) -> doc_text(int.to_string(n))
        l.Float(f) -> doc_text(float.to_string(f))
      }
    PLitT(doc_text) -> format_lit_type(doc_text)
    PAlias(ast.Pattern(PAny, _), name) -> doc_text(name)
    PAlias(inner, name) ->
      doc.concat([
        doc_pattern(inner, indent),
        doc_text("@"),
        doc_text(name),
      ])
    PCtr(tag, inner) ->
      doc.concat([
        doc_text("#" <> tag <> "("),
        doc_pattern(inner, indent),
        doc_text(")"),
      ])
    PRcd(fields) -> doc_pattern_rcd(fields, indent)
    PErr -> doc_text("%error")
    _ -> todo
  }
}

fn doc_pattern_rcd(fields: List(#(String, Pattern)), indent: Int) -> Document {
  case fields {
    [] -> doc_text("{}")
    [field] -> {
      let field_doc =
        doc.concat([doc_text(field.0 <> ": "), doc_pattern(field.1, indent)])
      doc.concat([doc_text("{"), field_doc, doc_text("}")])
    }
    _ -> {
      let field_docs =
        fields
        |> list.map(fn(f) {
          doc.concat([doc_text(f.0 <> ": "), doc_pattern(f.1, indent)])
        })
      doc.concat([
        doc_text("{"),
        doc.line,
        doc.nest(
          doc.join(field_docs, doc.concat([doc_text(","), doc.line])),
          indent,
        ),
        doc.line,
        doc_text("}"),
      ])
      |> doc.group
    }
  }
}

fn format_typedef(td: TypeDefinition, indent: Int) -> Document {
  let param_names =
    td.params
    |> list.map(fn(p) { p.0 })
    |> string.join(" ")
  let variant_docs =
    td.variants
    |> list.map(fn(v) { format_variant(v.1, indent) })
  doc.concat([
    doc_text("type "),
    doc_text(param_names),
    doc_text(" {"),
    doc.line,
    doc.nest(
      doc.join(variant_docs, doc.concat([doc_text("|"), doc.line])),
      indent,
    ),
    doc.line,
    doc_text("}"),
  ])
  |> doc.group
}

fn format_variant(v: Variant, indent: Int) -> Document {
  let param_names =
    v.params
    |> list.map(fn(p) { p.0 })
    |> string.join(" ")
  doc.concat([
    doc_text("| "),
    doc_text(param_names),
    doc_text(" -> "),
    doc_term(v.returns, indent),
  ])
}
