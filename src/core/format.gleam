import core/ast.{
  type Case, type Pattern, type Term, type Type, type TypeDefinition,
  type Variant, PAlias, PAny, PCtr, PErr, PLit, PLitT, PRcd, PTyp,
}
import core/literals.{type LiteralType} as l
import glam/doc.{type Document}
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string

pub fn format(term: Term, width: Int, indent: Int) -> String {
  doc_term(term, indent)
  |> doc.to_string(width)
}

fn doc_text(text: String) -> Document {
  doc.from_string(text)
}

fn doc_term(term: Term, indent: Int) -> Document {
  case term.data {
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
    ast.Var(name) -> doc_text(name)
    ast.Ctr(tag, arg) ->
      doc.concat([
        doc_text("#" <> tag <> "("),
        doc_term(arg, indent),
        doc_text(")"),
      ])
    ast.Rcd(fields) -> format_rcd(fields, indent)
    ast.RcdT(fields) -> format_rcdt(fields)
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
        doc_text("%fn"),
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
      let case_docs = list.map(cases, format_case)
      doc.concat([
        doc_text("%match "),
        doc_term(arg, indent),
        doc_text(" {"),
        doc.line,
        doc.nest(doc.join(case_docs, doc.concat([doc_text("|"), doc.line])), 2),
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
        doc.join(arg_docs, doc.concat([doc_text(", "), doc.space])),
        doc_text(")"),
      ])
    }
    ast.Let(#(name, opt_type, value), body) ->
      doc.concat([
        doc_text("%let "),
        doc_text(name),
        doc_text(": "),
        doc_opt_type(opt_type, indent),
        doc_text(" = "),
        doc_term(value, indent),
        doc_text("; "),
        doc_term(body, indent),
      ])
    ast.LetP(#(pattern, opt_type, value), body) ->
      doc.concat([
        doc_text("%let "),
        doc_pattern(pattern, indent),
        doc_opt_type(opt_type, indent),
        doc_text(" = "),
        doc_term(value, indent),
        doc_text("; "),
        doc_term(body, indent),
      ])
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

fn format_rcd(fields: List(#(String, Term)), indent: Int) -> Document {
  case fields {
    [] -> doc_text("{}")
    [field] -> {
      let field_doc =
        doc.concat([doc_text(field.0 <> ": "), doc_term(field.1, indent)])
      doc.concat([doc_text("{"), field_doc, doc_text("}")])
    }
    _ -> {
      let field_docs =
        fields
        |> list.map(fn(f) {
          doc.concat([doc_text(f.0 <> ": "), doc_term(f.1, indent)])
        })
      doc.concat([
        doc_text("{"),
        doc.nest(
          doc.concat([
            doc.line,
            doc.join(field_docs, doc.concat([doc_text(","), doc.line])),
          ]),
          indent,
        ),
        doc.line,
        doc_text("}"),
      ])
      |> doc.group
    }
  }
}

fn format_rcdt(
  fields: List(#(String, #(Option(Term), Option(Term)))),
) -> Document {
  todo
  // case fields {
  //   [] -> doc_text("%{}")
  //   [field] -> {
  //     let field_doc = case field.1.1 {
  //       Some(default_) ->
  //         doc.concat([
  //           doc_text(field.0 <> ": "),
  //           doc_term(field.1.0),
  //           doc_text(" = "),
  //           doc_term(default_),
  //         ])
  //       None -> doc.concat([doc_text(field.0 <> ": "), doc_term(field.1.0)])
  //     }
  //     doc.concat([doc_text("%{"), field_doc, doc_text("}")])
  //   }
  //   _ -> {
  //     let field_docs =
  //       fields
  //       |> list.map(fn(f) {
  //         let field_str = doc.concat([doc_text(f.0 <> ": "), doc_term(f.1.0)])
  //         case f.1.1 {
  //           Some(default_) -> doc.concat([field_str, doc_text(" = "), doc_term(default_)])
  //           None -> field_str
  //         }
  //       })
  //     doc.concat([
  //       doc_text("%{"),
  //       nest(
  //         doc.concat([
  //           doc.line(),
  //           doc.join(field_docs, doc.concat([doc_text(","), doc.line()])),
  //         ]),
  //       ),
  //       doc.line(),
  //       doc_text("}"),
  //     ])
  //     |> doc.group
  //   }
  // }
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

fn format_case(c: Case) -> Document {
  todo
  // let guard_doc = case c.guard {
  //   Some(#(guard, pass)) ->
  //     doc.concat([doc_text(" ? "), doc_term(guard), doc_text(" ~ "), doc_pattern(pass)])
  //   None -> doc_text("")
  // }
  // doc.concat([
  //   doc_text("| "),
  //   doc_pattern(c.pattern),
  //   guard_doc,
  //   doc_text(" => "),
  //   doc_term(c.body),
  // ])
}

fn doc_pattern(pattern: Pattern, indent: Int) -> Document {
  case pattern {
    PAny(_) -> doc_text("_")
    PTyp(u, _) ->
      case u {
        0 -> doc_text("%Type")
        n -> doc_text("%Type<" <> int.to_string(n) <> ">")
      }
    PLit(l, _) ->
      case l {
        l.Int(n) -> doc_text(int.to_string(n))
        l.Float(f) -> doc_text(float.to_string(f))
      }
    PLitT(doc_text, _) -> format_lit_type(doc_text)
    PAlias(name, inner, _) ->
      doc.concat([
        doc_text("_@"),
        doc_text(name),
        doc_text("@"),
        doc_pattern(inner, indent),
      ])
    PCtr(tag, inner, _) ->
      doc.concat([
        doc_text("#" <> tag <> "("),
        doc_pattern(inner, indent),
        doc_text(")"),
      ])
    PRcd(fields, _) -> doc_pattern_rcd(fields, indent)
    PErr(_) -> doc_text("%error")
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
