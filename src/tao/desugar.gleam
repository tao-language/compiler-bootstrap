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

pub const new_block_ctx = BlockCtx(
  on_break: None,
  on_continue: None,
  mutables: [],
)

pub fn desugar_expr(expr: Expr) -> Term {
  case expr.data {
    tao.Hole(id) -> core.hole(id, expr.span)
    tao.Lit(value) -> core.Term(core.Lit(value), expr.span)
    tao.Var(name) -> core.var(name, expr.span)
    tao.Ctr(tag, args) -> {
      let core_args = desugar_args(args)
      core.ctr(tag, core_args, expr.span)
    }
    tao.Rcd(fields) -> {
      let core_fields = desugar_rcd_fields(fields)
      core.rcd(core_fields, expr.span)
    }
    tao.RcdT(fields) -> {
      let core_fields = desugar_rcdt_fields(fields)
      core.rcd_t(core_fields, expr.span)
    }
    tao.Ann(value, type_) -> {
      let core_value = desugar_expr(value)
      let core_type = desugar_expr(type_)
      core.ann(core_value, core_type, expr.span)
    }
    tao.Fn(implicits, params, returns, body) ->
      desugar_fn(implicits, params, returns, body, expr.span)
    tao.FnT(implicits, params, body) ->
      desugar_fnt(implicits, params, body, expr.span)
    tao.App(fun, implicits, args) ->
      desugar_app(fun, implicits, args, expr.span)
    tao.Match(arg, cases) -> {
      let core_arg = desugar_expr(arg)
      let core_cases = desugar_case_list(cases)
      core.match(core_arg, core_cases, expr.span)
    }
    tao.Call(name, ret, args) -> {
      let core_ret = desugar_expr(ret)
      let core_args = list.map(args, desugar_expr)
      core.call(name, core_ret, core_args, expr.span)
    }
    tao.Do(block) -> desugar_block(block, expr.span)
    tao.Err -> core.err(expr.span)
  }
}

fn desugar_fn(
  implicits: List(tao.Param),
  params: List(tao.Param),
  returns: Option(tao.Type),
  body: Expr,
  span: Span,
) -> core.Term {
  case implicits, params {
    [], [] ->
      case returns {
        Some(type_) -> desugar_expr(tao.ann(body, type_, body.span))
        None -> desugar_expr(body)
      }
    _, _ -> todo
  }
}

fn desugar_fnt(
  implicits: List(tao.Param),
  params: List(tao.Param),
  body: Expr,
  span: Span,
) -> core.Term {
  todo
}

fn desugar_app(
  fun: Expr,
  implicits: List(#(String, Expr)),
  args: List(#(String, Expr)),
  span: Span,
) -> core.Term {
  todo
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

pub fn desugar_block(block: List(Stmt), span: Span) -> core.Term {
  desugar_stmt_list(new_block_ctx, block, span)
}

pub fn desugar_stmt_list(
  ctx: BlockCtx,
  stmts: List(Stmt),
  span: Span,
) -> core.Term {
  case stmts {
    [] -> core.rcd([], span)
    [stmt, ..stmts] -> {
      let next = desugar_stmt_list(ctx, stmts, span)
      desugar_stmt(ctx, stmt, next)
    }
  }
}

pub fn desugar_stmt(ctx: BlockCtx, stmt: Stmt, next: core.Term) -> core.Term {
  case stmt.data {
    tao.Let(pattern, opt_type, value) -> todo
    tao.LetMut(name, opt_type, value) -> todo
    tao.Mut(name, value) -> todo
    tao.FnDef(name, implicits, params, returns, body) -> {
      let core_fn = desugar_fn(implicits, params, returns, body, stmt.span)
      core.let_var(#(name, None, core_fn), next, stmt.span)
    }
    tao.TypeDef(type_def) -> todo
    tao.For(iterator, range, body) -> todo
    tao.While(condition, body) -> todo
    tao.Return(expr) -> desugar_expr(expr)
    tao.Break -> todo
    tao.Continue -> todo
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
