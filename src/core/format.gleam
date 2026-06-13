import core/ast.{
  type Case, type Pattern, type Term, type TypeDefinition, type Variant, PAlias,
  PAny, PCtr, PErr, PLit, PLitT, PRcd, PTyp,
}
import core/literals.{type LiteralType} as l
import glam/doc.{type Document}
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string

// ============================================================================
// Pretty-printing helpers
// ============================================================================

fn t(s: String) -> Document {
  doc.from_string(s)
}

// Concatenate a list of documents
fn docs(ds: List(Document)) -> Document {
  doc.concat(ds)
}

fn nl() -> Document {
  doc.line
}

fn nest(d: Document) -> Document {
  doc.nest(d, by: 2)
}

fn join_docs(ds: List(Document), sep: Document) -> Document {
  doc.join(ds, with: sep)
}

// ============================================================================
// AST formatting
// ============================================================================

pub fn format(term: Term, width: Int) -> String {
  format_term(term)
  |> doc.to_string(width)
}

fn format_term(term: Term) -> Document {
  case term.data {
    ast.Typ(u) ->
      case u {
        0 -> t("%Type")
        n -> t("%Type<" <> int.to_string(n) <> ">")
      }
    ast.Hole(None) -> t("?")
    ast.Hole(Some(id)) -> t("?<" <> int.to_string(id) <> ">")
    ast.Lit(l) ->
      case l {
        l.Int(value) -> t(int.to_string(value))
        l.Float(value) -> t(float.to_string(value))
      }
    ast.LitT(t_) -> format_lit_type(t_)
    ast.Var(name) -> t(name)
    ast.Ctr(tag, arg) -> docs([t("#" <> tag <> "("), format_term(arg), t(")")])
    ast.Rcd(fields) -> format_rcd(fields)
    ast.RcdT(fields) -> format_rcdt(fields)
    ast.Ann(term, type_) ->
      docs([t("%("), format_term(term), t(": "), format_term(type_), t(")")])
    ast.Lam(implicit, #(name, type_), body) -> {
      // let param = param_doc(implicit, name, format_term(type_))
      // docs([t("%fn"), param, t(" => "), format_term(body)])
      todo
    }
    ast.Pi(implicit, #(name, type_), body) -> {
      todo
      // let domain = param_doc(implicit, name, format_term(type_))
      // docs([t("%pi"), domain, t(" -> "), format_term(codomain)])
    }
    ast.Fix(name, body) ->
      docs([t("%fix "), t(name), t(". "), format_term(body)])
    ast.App(implicit, fun, arg) -> {
      let fun_doc = format_term(fun)
      let arg_doc = format_term(arg)
      case implicit {
        True -> docs([fun_doc, t("<"), arg_doc, t(">")])
        False -> docs([fun_doc, t("("), arg_doc, t(")")])
      }
    }
    ast.TypeDef(type_def) -> format_typedef(type_def)
    ast.Let(#(name, type_, value), body) ->
      // docs([
      //   t("%let "),
      //   t(name),
      //   t(": "),
      //   format_term(type_),
      //   t(" = "),
      //   format_term(value),
      //   t("; "),
      //   format_term(body),
      // ])
      todo
    ast.LetP(#(pattern, type_, value), body) ->
      // docs([
      //   t("%let "),
      //   t(todo as "LetP pattern"),
      //   t(": "),
      //   format_term(type_),
      //   t(" = "),
      //   format_term(value),
      //   t("; "),
      //   format_term(body),
      // ])
      todo
    ast.Match(arg, cases) -> {
      let case_docs = cases |> list.map(format_case)
      docs([
        t("%match "),
        format_term(arg),
        t(" {"),
        nl(),
        nest(join_docs(case_docs, docs([t("|"), nl()]))),
        nl(),
        t("}"),
      ])
      |> doc.group
    }
    ast.Call(name, returns, args) -> {
      let arg_docs = args |> list.map(format_term)
      docs([
        t("@"),
        t(name),
        t("<"),
        format_term(returns),
        t(">"),
        t("("),
        join_docs(arg_docs, docs([t(","), doc.space])),
        t(")"),
      ])
    }
    ast.Err -> t("%error")
  }
}

fn format_rcd(fields: List(#(String, Term))) -> Document {
  case fields {
    [] -> t("{}")
    [field] -> {
      let field_doc = docs([t(field.0 <> ": "), format_term(field.1)])
      docs([t("{"), field_doc, t("}")])
    }
    _ -> {
      let field_docs =
        fields
        |> list.map(fn(f) { docs([t(f.0 <> ": "), format_term(f.1)]) })
      docs([
        t("{"),
        nest(
          docs([
            nl(),
            join_docs(field_docs, docs([t(","), nl()])),
          ]),
        ),
        nl(),
        t("}"),
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
  //   [] -> t("%{}")
  //   [field] -> {
  //     let field_doc = case field.1.1 {
  //       Some(default_) ->
  //         docs([
  //           t(field.0 <> ": "),
  //           format_term(field.1.0),
  //           t(" = "),
  //           format_term(default_),
  //         ])
  //       None -> docs([t(field.0 <> ": "), format_term(field.1.0)])
  //     }
  //     docs([t("%{"), field_doc, t("}")])
  //   }
  //   _ -> {
  //     let field_docs =
  //       fields
  //       |> list.map(fn(f) {
  //         let field_str = docs([t(f.0 <> ": "), format_term(f.1.0)])
  //         case f.1.1 {
  //           Some(default_) -> docs([field_str, t(" = "), format_term(default_)])
  //           None -> field_str
  //         }
  //       })
  //     docs([
  //       t("%{"),
  //       nest(
  //         docs([
  //           nl(),
  //           join_docs(field_docs, docs([t(","), nl()])),
  //         ]),
  //       ),
  //       nl(),
  //       t("}"),
  //     ])
  //     |> doc.group
  //   }
  // }
}

fn param_doc(implicit: Bool, name: String, type_: Document) -> Document {
  case implicit {
    True -> docs([t("<"), t(name), t(": "), type_, t(">")])
    False -> docs([t("("), t(name), t(": "), type_, t(")")])
  }
}

fn format_lit_type(lt: LiteralType) -> Document {
  case lt {
    _ if lt == l.IntT -> t("%Int")
    _ if lt == l.FloatT -> t("%Float")
    _ if lt == l.I8 -> t("%I8")
    _ if lt == l.I16 -> t("%I16")
    _ if lt == l.I32 -> t("%I32")
    _ if lt == l.I64 -> t("%I64")
    _ if lt == l.U8 -> t("%U8")
    _ if lt == l.U16 -> t("%U16")
    _ if lt == l.U32 -> t("%U32")
    _ if lt == l.U64 -> t("%U64")
    _ if lt == l.F16 -> t("%F16")
    _ if lt == l.F32 -> t("%F32")
    _ -> t("%F64")
  }
}

fn format_case(c: Case) -> Document {
  todo
  // let guard_doc = case c.guard {
  //   Some(#(guard, pass)) ->
  //     docs([t(" ? "), format_term(guard), t(" ~ "), format_pattern(pass)])
  //   None -> t("")
  // }
  // docs([
  //   t("| "),
  //   format_pattern(c.pattern),
  //   guard_doc,
  //   t(" => "),
  //   format_term(c.body),
  // ])
}

fn format_pattern(pattern: Pattern) -> Document {
  case pattern {
    PAny(_) -> t("_")
    PTyp(u, _) ->
      case u {
        0 -> t("%Type")
        n -> t("%Type<" <> int.to_string(n) <> ">")
      }
    PLit(l, _) ->
      case l {
        l.Int(n) -> t(int.to_string(n))
        l.Float(f) -> t(float.to_string(f))
      }
    PLitT(t, _) -> format_lit_type(t)
    PAlias(name, inner, _) ->
      docs([t("_@"), t(name), t("@"), format_pattern(inner)])
    PCtr(tag, inner, _) ->
      docs([t("#" <> tag <> "("), format_pattern(inner), t(")")])
    PRcd(fields, _) -> format_pattern_rcd(fields)
    PErr(_) -> t("%error")
    _ -> todo
  }
}

fn format_pattern_rcd(fields: List(#(String, Pattern))) -> Document {
  case fields {
    [] -> t("{}")
    [field] -> {
      let field_doc = docs([t(field.0 <> ": "), format_pattern(field.1)])
      docs([t("{"), field_doc, t("}")])
    }
    _ -> {
      let field_docs =
        fields
        |> list.map(fn(f) { docs([t(f.0 <> ": "), format_pattern(f.1)]) })
      docs([
        t("{"),
        nl(),
        nest(join_docs(field_docs, docs([t(","), nl()]))),
        nl(),
        t("}"),
      ])
      |> doc.group
    }
  }
}

fn format_typedef(td: TypeDefinition) -> Document {
  let param_names =
    td.params
    |> list.map(fn(p) { p.0 })
    |> string.join(" ")
  let variant_docs =
    td.variants
    |> list.map(fn(v) { format_variant(v.1) })
  docs([
    t("type "),
    t(param_names),
    t(" {"),
    nl(),
    nest(join_docs(variant_docs, docs([t("|"), nl()]))),
    nl(),
    t("}"),
  ])
  |> doc.group
}

fn format_variant(v: Variant) -> Document {
  let param_names =
    v.params
    |> list.map(fn(p) { p.0 })
    |> string.join(" ")
  docs([t("| "), t(param_names), t(" -> "), format_term(v.returns)])
}
