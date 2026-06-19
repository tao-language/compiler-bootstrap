import core/ast as core
import filepath
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import syntax/span.{type Span, Span}
import tao/ast.{type Case, type Module, type Pattern, type Stmt} as tao
import tao/discover

pub type BlockCtx {
  BlockCtx(
    on_break: Option(tao.Expr),
    on_continue: Option(tao.Expr),
    mutables: List(String),
  )
}

pub const new_block_ctx = BlockCtx(
  on_break: None,
  on_continue: None,
  mutables: [],
)

pub fn expr(e: tao.Expr) -> core.Expr {
  case e.data {
    tao.Hole(id) -> core.hole(id, e.span)
    tao.Lit(value) -> core.Expr(core.Lit(value), e.span)
    tao.Var(name) -> core.var(name, e.span)
    tao.Ctr("Int", []) -> core.int_t(e.span)
    tao.Ctr("Float", []) -> core.float_t(e.span)
    tao.Ctr(tag, args) -> {
      let core_args = arguments(args)
      core.ctr(tag, core_args, e.span)
    }
    tao.Rcd(fields) -> {
      let core_fields = rcd_fields(fields)
      core.rcd(core_fields, e.span)
    }
    tao.RcdT(fields) -> {
      let core_fields = rcdt_fields(fields)
      core.rcd_t(core_fields, e.span)
    }
    tao.Ann(value, type_) -> {
      let core_value = expr(value)
      let core_type = expr(type_)
      core.ann(core_value, core_type, e.span)
    }
    tao.Fn(implicits, params, returns, body) ->
      function(None, implicits, params, returns, body, e.span)
    tao.FnT(implicits, params, body) ->
      function_type(implicits, params, body, e.span)
    tao.App(fun, args) -> application(False, fun, args, e.span)
    tao.AppImplicits(fun, args) -> application(True, fun, args, e.span)
    tao.Match(arg, cases) -> {
      let core_arg = expr(arg)
      let core_cases = case_list(cases)
      core.match(core_arg, core_cases, e.span)
    }
    tao.Op1(op, expr) -> todo
    tao.Op2(op, lhs, rhs) -> todo
    tao.Call(name, ret, args) -> {
      let core_ret = expr(ret)
      let core_args = list.map(args, expr)
      core.call(name, core_ret, core_args, e.span)
    }
    tao.Do(block) -> {
      let return = core.rcd([], e.span)
      statement_list(new_block_ctx, block, return)
    }
    tao.Err -> core.err(e.span)
  }
}

fn opt_expr(opt_expr: Option(tao.Expr)) -> Option(core.Expr) {
  option.map(opt_expr, expr)
}

fn arguments(args: List(#(String, tao.Expr))) -> core.Expr {
  let core_params =
    core.Rcd(
      list.index_map(args, fn(named_arg, index) {
        let #(name, arg) = named_arg
        let name = case name {
          "" -> int.to_string(index + 1)
          _ -> name
        }
        #(name, expr(arg))
      }),
    )
  // TODO: span.merge(first_span, last_span)
  core.Expr(core_params, Span("", 0, 0, 0, 0))
}

fn function(
  opt_fun_name: Option(String),
  implicits: List(tao.Param),
  params: List(tao.Param),
  opt_returns: Option(tao.Type),
  body: tao.Expr,
  span: Span,
) -> core.Expr {
  case implicits {
    [] -> {
      let param_name = "_"
      // TODO: infer span from args
      let args_span = span
      let param_fields =
        list.index_map(params, fn(param, index) {
          let #(_, #(opt_type, opt_default)) = param
          let core_type = opt_expr(opt_type)
          let core_default = opt_expr(opt_default)
          #(int.to_string(index + 1), #(core_type, core_default))
        })
      let core_param_type = core.rcd_t(param_fields, args_span)
      let bindings =
        list.index_map(params, fn(param, index) {
          let #(p, _) = param
          #(int.to_string(index + 1), p)
        })
      let unpack = tao.Case(tao.prcd(bindings, args_span), body)
      let core_body =
        expr(tao.match(tao.var(param_name, args_span), [unpack], span))
      let core_body = case opt_returns {
        None -> core_body
        Some(returns) -> {
          let core_body_type = expr(returns)
          core.ann(core_body, core_body_type, returns.span)
        }
      }
      let core_fun =
        core.lam(#(param_name, Some(core_param_type)), core_body, span)
      case opt_fun_name {
        Some(fun_name) -> core.fix(fun_name, core_fun, span)
        None -> core_fun
      }
    }
    _ -> todo
  }
}

fn function_type(
  implicits: List(tao.Param),
  params: List(tao.Param),
  body: tao.Expr,
  span: Span,
) -> core.Expr {
  todo
}

fn application(
  implicit: Bool,
  fun: tao.Expr,
  args: List(#(String, tao.Expr)),
  span: Span,
) -> core.Expr {
  let core_fun = expr(fun)
  let core_args = arguments(args)
  core.Expr(core.App(implicit, core_fun, core_args), span)
}

fn case_list(cases: List(tao.Case)) -> List(core.Case) {
  list.map(cases, case_)
}

fn case_(c: tao.Case) -> core.Case {
  case c {
    tao.Case(p, body) -> core.Case(pattern(p), None, expr(body))
    tao.CaseIf(p, guard, body) -> {
      let guard = tao.ann(guard, tao.bool(guard.span), guard.span)
      let guard_pat = tao.pctr("True", [], guard.span)
      case_(tao.CaseIfMatch(p, #(guard, guard_pat), body))
    }
    tao.CaseIfMatch(p, #(guard_expr, guard_pattern), body) -> {
      let guard_tm = expr(guard_expr)
      let guard_pat = pattern(guard_pattern)
      core.Case(pattern(p), Some(#(guard_tm, guard_pat)), expr(body))
    }
  }
}

fn pattern(p: Pattern) -> core.Pattern {
  case p.data {
    tao.PAny -> core.pany(p.span)
    tao.PVar(name) -> core.pvar(name, p.span)
    tao.PLit(l) -> core.Pattern(core.PLit(l), p.span)
    tao.PLitT(t) -> core.Pattern(core.PLitT(t), p.span)
    tao.PRcd(fields) -> {
      let core_fields =
        list.map(fields, fn(field) {
          let #(name, p) = field
          #(name, pattern(p))
        })
      core.prcd(core_fields, p.span)
    }
    tao.PRcdT(fields) -> {
      let core_fields =
        list.map(fields, fn(field) {
          let #(name, p) = field
          #(name, pattern(p))
        })
      core.prcd_t(core_fields, p.span)
    }
    tao.PCtr(tag, args) -> {
      let core_fields =
        list.map(args, fn(field) {
          let #(name, p) = field
          #(name, pattern(p))
        })
      core.pctr(tag, core.prcd(core_fields, p.span), p.span)
    }
  }
}

pub fn module(mod: Module) -> core.Expr {
  let #(name, stmts) = mod
  let exports =
    discover.definitions(stmts)
    |> list.filter(fn(name) { !string.starts_with(name, "_") })
  let mod_return = core.rcd_vars(exports, Span(name, 0, 0, 0, 0))
  statement_list(new_block_ctx, stmts, mod_return)
}

pub fn statement_list(
  ctx: BlockCtx,
  stmts: List(Stmt),
  return: core.Expr,
) -> core.Expr {
  case stmts {
    [] -> return
    [stmt, ..stmts] -> {
      let next = statement_list(ctx, stmts, return)
      statement(ctx, stmt, next)
    }
  }
}

pub fn statement(ctx: BlockCtx, stmt: Stmt, next: core.Expr) -> core.Expr {
  case stmt.data {
    tao.Import(path, opt_alias, []) -> {
      let alias = case opt_alias {
        Some(alias) -> alias
        None -> filepath.base_name(path)
      }
      let def = #(alias, None, core.var("@" <> path, stmt.span))
      core.let_var(def, next, stmt.span)
    }
    tao.Import(path, opt_alias, [#(name, opt_name_alias), ..names]) -> {
      let stmt = tao.import_(path, opt_alias, names, stmt.span)
      let name_alias = case opt_name_alias {
        Some(alias) -> alias
        None -> name
      }
      let access = core.dot(core.var("@" <> path, stmt.span), name, stmt.span)
      let next = core.let_var(#(name_alias, None, access), next, stmt.span)
      statement(ctx, stmt, next)
    }
    tao.Let(p, opt_type, value) -> {
      let core_pattern = pattern(p)
      let core_type = opt_expr(opt_type)
      let core_value = expr(value)
      core.let_pat(#(core_pattern, core_type, core_value), next, stmt.span)
    }
    tao.LetMut(name, opt_type, value) -> todo
    tao.Mut(name, value) -> todo
    tao.FnDef(name, implicits, params, returns, body) -> {
      let core_fn =
        function(Some(name), implicits, params, returns, body, stmt.span)
      core.let_var(#(name, None, core_fn), next, stmt.span)
    }
    tao.TypeDef(type_def) -> todo
    tao.For(iterator, range, body) -> todo
    tao.While(condition, body) -> todo
    tao.Return(ret_expr) -> expr(ret_expr)
    tao.Break -> todo
    tao.Continue -> todo
  }
}

fn rcd_fields(fields: List(#(String, tao.Expr))) -> List(#(String, core.Expr)) {
  list.map(fields, fn(f) {
    let #(name, arg) = f
    #(name, expr(arg))
  })
}

fn rcdt_fields(
  fields: List(#(String, #(Option(tao.Type), Option(tao.Expr)))),
) -> List(#(String, #(Option(core.Type), Option(core.Expr)))) {
  list.map(fields, fn(f) {
    let #(name, #(type_, default_)) = f
    let type_term = case type_ {
      None -> None
      Some(t) -> Some(expr(t))
    }
    let default_term = case default_ {
      None -> None
      Some(e) -> Some(expr(e))
    }
    #(name, #(type_term, default_term))
  })
}
