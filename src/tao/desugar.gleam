import core/ast.{type Term, Term} as core
import gleam/list
import gleam/option.{type Option, None, Some}
import tao/ast.{type Case, type Expr, type Pattern, type Stmt} as tao

pub type BlockCtx {
  BlockCtx(
    on_break: Option(Term),
    on_continue: Option(Term),
    mutables: List(String),
  )
}

pub fn desugar_expr(expr: Expr) -> Term {
  let data = case expr.data {
    tao.Hole(id) -> core.Hole(id)
    tao.Lit(value) -> core.Lit(value)
    tao.Var(name) -> core.Var(name)
    tao.Ctr(tag, args) -> core.Ctr(tag, desugar_args(args))
    tao.Rcd(fields) -> core.Rcd(desugar_rcd_fields(fields))
    tao.RcdT(fields) -> core.RcdT(desugar_rcdt_fields(fields))
    tao.Ann(value, type_) -> core.Ann(desugar_expr(value), desugar_expr(type_))
    tao.Fn(_, _, _, _) -> todo
    tao.FnT(_, _, _) -> todo
    tao.App(fun, implicits, args) -> todo
    tao.Match(arg, cases) -> todo
    tao.Call(name, ret, args) -> todo
    tao.Do(block) -> desugar_block(block)
    tao.Err -> core.Err
  }
  Term(data, expr.span)
}

pub fn desugar_block(block: List(Stmt)) -> core.TermData {
  todo
}

fn desugar_args(args: List(#(String, Expr))) -> core.Term {
  todo
}

fn desugar_rcd_fields(fields: List(#(String, Expr))) -> List(#(String, Term)) {
  todo
}

fn desugar_rcdt_fields(
  fields: List(#(String, #(Option(Expr), Option(Expr)))),
) -> List(#(String, #(Option(Term), Option(Term)))) {
  todo
}
// fn desugar_pattern(p: Pattern) -> core.Pattern {
//   case p.data {
//     PAny -> core.PAny(p.span)
//     PVar(name) -> core.PAlias(name, core.PAny(p.span), p.span)
//     PLit(l) -> core.PLit(l, p.span)
//     PLitT(t) -> core.PLitT(t, p.span)
//     PCtr(tag, args) -> {
//       let inner = case args {
//         [] -> core.PAny(p.span)
//         [#(_, inner_pat)] -> desugar_pattern(inner_pat)
//         _ -> core.PAny(p.span)
//       }
//       core.PCtr(tag, inner, p.span)
//     }
//   }
// }

// fn desugar_cases(cases: List(tao.Case)) -> List(core.Case) {
//   list.map(cases, fn(c) {
//     case c {
//       tao.Case(pattern, body) ->
//         core.Case(
//           pattern: desugar_pattern(pattern),
//           guard: None,
//           body: desugar_expr(body),
//           span: pattern.span,
//         )
//       tao.CaseIf(pattern, guard, body) -> {
//         let guard_Term = desugar_expr(guard)
//         core.Case(
//           pattern: desugar_pattern(pattern),
//           guard: Some(#(guard_Term, core.PAny(pattern.span))),
//           body: desugar_expr(body),
//           span: pattern.span,
//         )
//       }
//       tao.CaseIfMatch(pattern, guard, body) -> {
//         let #(guard_expr, guard_pat) = guard
//         core.Case(
//           pattern: desugar_pattern(pattern),
//           guard: Some(#(desugar_expr(guard_expr), desugar_pattern(guard_pat))),
//           body: desugar_expr(body),
//           span: pattern.span,
//         )
//       }
//     }
//   })
// }
