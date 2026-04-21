// ============================================================================
// CORE AST STRING - Term/Value/Literal to String Conversion
// ============================================================================
import gleam/float
import gleam/int
import gleam/list
import gleam/string
import core/ast as ast

pub fn literal_to_string(lit: ast.Literal) -> String {
  case lit {
    ast.I32(n) -> int.to_string(n)
    ast.I64(n) -> int.to_string(n)
    ast.U32(n) -> int.to_string(n)
    ast.U64(n) -> int.to_string(n)
    ast.F32(f) -> float.to_string(f)
    ast.F64(f) -> float.to_string(f)
    ast.IntLit(n) -> int.to_string(n)
    ast.FloatLit(f) -> float.to_string(f)
  }
}

pub fn literal_type_to_string(lit: ast.LiteralType) -> String {
  case lit {
    ast.I32T -> "I32"
    ast.I64T -> "I64"
    ast.U32T -> "U32"
    ast.U64T -> "U64"
    ast.F32T -> "F32"
    ast.F64T -> "F64"
    ast.ILitT -> "Int"
    ast.FLitT -> "Float"
  }
}

pub fn value_to_string(val: ast.Value) -> String {
  case val {
    ast.VUnit -> "Unit"
    ast.VTyp(_) -> "Type"
    ast.VLit(lit) -> literal_to_string(lit)
    ast.VLitT(lit) -> literal_type_to_string(lit)
    ast.VNeut(head, _) -> head_to_string(head)
    ast.VRcd(_) -> "{...}"
    ast.VCtrValue(ctr) -> ctr_to_string(ctr)
    ast.VLam(_, _, _, _) -> "λ"
    ast.VPi(_, _, _, domain, _) -> "(" <> type_to_string(domain) <> ") -> ..."
    ast.VRecord(_) -> "Record{...}"
    ast.VCall(name, _, _) -> name <> "(...)"
    ast.VFix(_, _, _) -> "fix"
    ast.VErr -> "⊥"
  }
}

fn ctr_to_string(ctr: ast.CtrValue) -> String {
  case ctr {
    ast.VCtr(tag, ast.VUnit) -> tag
    ast.VCtr(tag, arg) -> "#" <> tag <> "(" <> value_to_string(arg) <> ")"
  }
}

pub fn head_to_string(head: ast.Head) -> String {
  case head {
    ast.HVar(index) -> "var[" <> int.to_string(index) <> "]"
    ast.HHole(id) -> "hole[" <> int.to_string(id) <> "]"
    ast.HStepLimit -> "<step-limit>"
  }
}

pub fn type_to_string(ty: ast.Type) -> String {
  case ty {
    ast.VTyp(_) -> "Type"
    ast.VLit(lit) -> literal_to_string(lit)
    ast.VLitT(lit) -> literal_type_to_string(lit)
    ast.VNeut(head, _) -> head_to_string(head)
    ast.VRcd(_) -> "{...}"
    ast.VCtrValue(ctr) -> ctr_to_string(ctr)
    ast.VLam(_, _, _, _) -> "λ"
    ast.VPi(_, _, _, domain, _) -> "(" <> type_to_string(domain) <> ") -> ..."
    ast.VRecord(_) -> "Record{...}"
    ast.VCall(name, _, _) -> name
    ast.VFix(_, _, _) -> "fix"
    ast.VUnit -> "Unit"
    ast.VErr -> "⊥"
  }
}

pub fn pattern_to_string(pattern: ast.Pattern) -> String {
  case pattern {
    ast.PAny -> "_"
    ast.PAs(pat, name) -> name <> "@" <> pattern_to_string(pat)
    ast.PTyp(level) -> case level {
      0 -> "%Type"
      n -> "%Type" <> int.to_string(n)
    }
    ast.PLit(lit) -> literal_to_string(lit)
    ast.PLitT(lit) -> literal_type_to_string(lit)
    ast.PRcd(fields) -> "{ " <> list.map(fields, fn(f) { f.0 <> " = ..." })
    |> string.join(", ") <> " }"
    ast.PCtr(tag, arg) -> tag <> "(" <> pattern_to_string(arg) <> ")"
    ast.PUnit -> "Unit"
  }
}

pub fn term_to_string(term: ast.Term) -> String {
  case term {
    ast.Lam(_, param, body, _) -> {
      let #(name, _) = param
      "λ" <> name <> " -> " <> term_to_string(body)
    }
    ast.App(fun, _, arg, _) ->
      term_to_string(fun) <> "(" <> term_to_string(arg) <> ")"
    ast.Let(name, value, body, _) ->
      "let " <> name <> " = " <> term_to_string(value) <> " -> " <> term_to_string(body)
    ast.Ctr(tag, arg, _) ->
      case arg {
        ast.Unit(_) -> tag
        _ -> tag <> "(" <> term_to_string(arg) <> ")"
      }
    ast.Rcd(fields, _) ->
      "{ " <> list.map(fields, fn(f) { f.0 <> " = " <> term_to_string(f.1) })
      |> string.join(", ") <> " }"
    ast.Ann(term, typ, _) ->
      term_to_string(term) <> " : " <> term_to_string(typ)
    ast.Pi(_, name, in_term, out_term, _) ->
      "\\" <> name <> " : " <> term_to_string(in_term) <> " -> " <> term_to_string(out_term)
    ast.Match(arg, _, cases, _) ->
      "match " <> term_to_string(arg) <> " with { " <>
      list.map(cases, fn(c) { pattern_to_string(c.pattern) <> " -> ..." })
      |> string.join(", ") <> " }"
    ast.Call(name, typed_args, ret, _) ->
      name <> "(" <> list.map(typed_args, fn(pair) { term_to_string(pair.0) }) |> string.join(", ") <> ") -> " <> term_to_string(ret)
    ast.Comptime(term, _) -> "#" <> term_to_string(term)
    ast.Fix(name, body, _) -> "fix " <> name
    ast.Typ(level, _) -> case level {
      0 -> "Type"
      n -> "Type" <> int.to_string(n)
    }
    ast.Lit(lit, _) -> literal_to_string(lit)
    ast.LitT(lit, _) -> literal_type_to_string(lit)
    ast.Var(index, _) -> "var[" <> int.to_string(index) <> "]"
    ast.Hole(id, _) -> "hole[" <> int.to_string(id) <> "]"
    ast.Err(message, _) -> message
    ast.Unit(_) -> "Unit"
    ast.Dot(term, field, _) -> term_to_string(term) <> "." <> field
  }
}
