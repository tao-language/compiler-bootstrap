import core/ast.{type Term, Term} as core
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span, Span}
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
    tao.Fn(implicits, params, returns, body) ->
      desugar_fn_data(implicits, params, returns, body, expr.span)
    tao.FnT(implicits, params, body) ->
      desugar_fnt_data(implicits, params, body, expr.span)
    tao.App(fun, implicits, args) ->
      desugar_app_data(fun, implicits, args, expr.span)
    tao.Match(arg, cases) ->
      core.Match(desugar_expr(arg), desugar_case_list(cases))
    tao.Call(name, ret, args) ->
      core.Call(name, desugar_expr(ret), list.map(args, desugar_expr))
    tao.Do(block) -> desugar_block(block)
    tao.Err -> core.Err
  }
  core.Term(data, expr.span)
}

fn desugar_fn_data(
  implicits: List(tao.Param),
  params: List(tao.Param),
  returns: Option(tao.Type),
  body: Expr,
  span: Span,
) -> core.TermData {
  let body_term = desugar_expr(body)
  case params {
    [] -> body_term.data
    [param, ..rest] -> {
      let #(pvar, #(_, _)) = param
      let param_name = case pvar.data {
        tao.PVar(n) -> n
        _ -> "_"
      }
      let rest_term = case rest {
        [] -> body_term
        _ -> core.Term(desugar_fn_data([], rest, None, body, span), span)
      }
      core.Lam(False, #(param_name, None), rest_term)
    }
  }
}

fn desugar_fnt_data(
  implicits: List(tao.Param),
  params: List(tao.Param),
  body: Expr,
  span: Span,
) -> core.TermData {
  let body_term = desugar_expr(body)
  case params {
    [] -> body_term.data
    [param, ..rest] -> {
      let #(pvar, #(_, _)) = param
      let param_name = case pvar.data {
        tao.PVar(n) -> n
        _ -> "_"
      }
      let rest_term = case rest {
        [] -> body_term
        _ -> core.Term(desugar_fnt_data([], rest, body, span), span)
      }
      core.Pi(False, #(param_name, None), rest_term)
    }
  }
}

fn desugar_app_data(
  fun: Expr,
  implicits: List(#(String, Expr)),
  args: List(#(String, Expr)),
  span: Span,
) -> core.TermData {
  let fun_term = desugar_expr(fun)
  case args {
    [] -> fun_term.data
    [arg, ..rest] -> {
      let #(name, arg_expr) = arg
      let arg_term = desugar_expr(arg_expr)
      let rest_term = case rest {
        [] -> fun_term
        _ -> core.Term(desugar_app_data(fun, implicits, rest, span), span)
      }
      core.App(False, rest_term, arg_term)
    }
  }
}

fn desugar_case_list(cases: List(tao.Case)) -> List(core.Case) {
  list.map(cases, desugar_case)
}

fn desugar_case(case_: tao.Case) -> core.Case {
  case case_ {
    tao.Case(pattern, body) ->
      core.Case(
        pattern: desugar_pattern(pattern),
        guard: None,
        body: desugar_expr(body),
      )
    tao.CaseIf(pattern, guard, body) -> {
      let guard = tao.ann(guard, tao.bool(guard.span), guard.span)
      let guard_pat = tao.pctr("True", [], guard.span)
      desugar_case(tao.CaseIfMatch(pattern, #(guard, guard_pat), body))
    }
    tao.CaseIfMatch(pattern, #(guard_expr, guard_pattern), body) -> {
      let guard_tm = desugar_expr(guard_expr)
      let guard_pat = desugar_pattern(guard_pattern)
      core.Case(
        pattern: desugar_pattern(pattern),
        guard: Some(#(guard_tm, guard_pat)),
        body: desugar_expr(body),
      )
    }
  }
}

fn desugar_pattern(p: Pattern) -> core.Pattern {
  case p.data {
    tao.PAny -> core.pany(p.span)
    tao.PVar(name) -> core.pvar(name, p.span)
    tao.PLit(l) -> core.Pattern(core.PLit(l), p.span)
    tao.PLitT(t) -> core.Pattern(core.PLitT(t), p.span)
    tao.PCtr(tag, args) -> {
      let inner = case args {
        [] -> core.pany(p.span)
        [#(_, inner_pat)] -> desugar_pattern(inner_pat)
        _ -> core.pany(p.span)
      }
      core.pctr(tag, inner, p.span)
    }
  }
}

pub fn desugar_block(block: List(Stmt)) -> core.TermData {
  case block {
    [] -> core.Err
    [stmt, ..rest] ->
      case stmt.data {
        tao.Let(pattern, type_, value) -> {
          let pattern_name = case pattern.data {
            tao.PVar(n) -> n
            _ -> "_"
          }
          let value_term = desugar_expr(value)
          let body_term = desugar_block(rest)
          let opt_type = case type_ {
            None -> None
            Some(t) -> Some(desugar_expr(t))
          }
          core.Let(
            #(pattern_name, opt_type, value_term),
            core.Term(body_term, stmt.span),
          )
        }
        tao.LetMut(name, type_, value) -> {
          let value_term = desugar_expr(value)
          let body_term = desugar_block(rest)
          let opt_type = case type_ {
            None -> None
            Some(t) -> Some(desugar_expr(t))
          }
          core.Let(
            #(name, opt_type, value_term),
            core.Term(body_term, stmt.span),
          )
        }
        tao.Mut(name, value) -> {
          let _value_term = desugar_expr(value)
          desugar_block(rest)
        }
        tao.FnDef(name, implicits, params, returns, body) -> {
          let fn_body =
            desugar_fn_data(implicits, params, returns, body, stmt.span)
          let rest_data = desugar_block(rest)
          core.Let(
            #(name, None, core.Term(fn_body, stmt.span)),
            core.Term(rest_data, stmt.span),
          )
        }
        tao.TypeDef(_) -> desugar_block(rest)
        tao.For(_, _, _) -> desugar_block(rest)
        tao.While(_, _) -> desugar_block(rest)
        tao.Return(expr) -> desugar_expr(expr).data
        tao.Break -> core.Err
        tao.Continue -> core.Err
      }
  }
}

fn desugar_args(args: List(#(String, Expr))) -> Term {
  let rcd =
    core.Rcd(
      list.map(args, fn(arg) {
        let #(name, expr) = arg
        #(name, desugar_expr(expr))
      }),
    )
  core.Term(rcd, Span("", 0, 0, 0, 0))
}

fn desugar_rcd_fields(fields: List(#(String, Expr))) -> List(#(String, Term)) {
  list.map(fields, fn(f) {
    let #(name, expr) = f
    #(name, desugar_expr(expr))
  })
}

fn desugar_rcdt_fields(
  fields: List(#(String, #(Option(Expr), Option(Expr)))),
) -> List(#(String, #(Option(Term), Option(Term)))) {
  list.map(fields, fn(f) {
    let #(name, #(type_, default_)) = f
    let type_term = case type_ {
      None -> None
      Some(t) -> Some(desugar_expr(t))
    }
    let default_term = case default_ {
      None -> None
      Some(e) -> Some(desugar_expr(e))
    }
    #(name, #(type_term, default_term))
  })
}
