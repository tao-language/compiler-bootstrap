import core/ast as core
import core/format
import filepath
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span, Span}
import tao/ast.{type Case, type Module, type Pattern, type Stmt} as tao

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

pub fn module(mod: Module, exports: List(String)) -> core.Expr {
  let #(mod_name, stmts) = mod
  let span = Span(mod_name, 0, 0, 0, 0)
  let return_expr = core.rcd_vars(exports, None, span)
  statement_list(new_block_ctx, stmts, return_expr)
}

pub fn expr(e: tao.Expr) -> core.Expr {
  case e.data {
    tao.Hole(id) -> core.hole(id, e.span)
    tao.Lit(value) -> core.Expr(core.Lit(value), e.span)
    tao.Var(name) -> core.var(name, e.span)
    tao.Ctr("Int", [], None) -> core.int_t(e.span)
    tao.Ctr("Float", [], None) -> core.float_t(e.span)
    tao.Ctr(tag, args, tail) -> {
      let core_args = arguments(args, tail, e.span)
      core.ctr(tag, core_args, e.span)
    }
    tao.Rcd(fields, tail) -> {
      let core_fields = rcd_fields(fields)
      let core_tail = opt_expr(tail)
      core.rcd_values(core_fields, core_tail, e.span)
    }
    tao.RcdT(fields, tail) -> {
      let core_fields = rcdt_fields(fields)
      let core_tail = opt_expr(tail)
      core.rcd(core_fields, core_tail, e.span)
    }
    tao.Ann(value, type_) -> {
      let core_value = expr(value)
      let core_type = expr(type_)
      core.ann(core_value, core_type, e.span)
    }
    tao.Fn(implicits, implicits_tail, params, params_tail, returns, body) ->
      function(
        None,
        implicits,
        implicits_tail,
        params,
        params_tail,
        returns,
        body,
        e.span,
      )
    tao.FnT(implicits, params, body) ->
      function_type(implicits, params, body, e.span)
    tao.App(fun, args, tail) -> application(fun, args, tail, e.span)
    tao.Match(arg, cases) -> {
      let core_arg = expr(arg)
      let core_cases = case_list(cases)
      core.match(core_arg, core_cases, e.span)
    }
    tao.Op1(op, expr) -> {
      echo e.data
      todo
    }
    tao.Op2(op, lhs, rhs) -> {
      let op_name = tao.binop_name(op)
      expr(tao.app(tao.var(op_name, e.span), [#("", lhs), #("", rhs)], e.span))
    }
    tao.Call(name, ret, args) -> {
      let core_ret = expr(ret)
      let core_args = list.map(args, expr)
      core.call(name, core_ret, core_args, e.span)
    }
    tao.Do(block) -> {
      let return = core.rcd([], None, e.span)
      statement_list(new_block_ctx, block, return)
    }
    tao.Err -> core.err(e.span)
  }
}

fn opt_expr(opt_expr: Option(tao.Expr)) -> Option(core.Expr) {
  option.map(opt_expr, expr)
}

fn arguments(
  args: List(#(String, tao.Expr)),
  tail: Option(tao.Expr),
  span: Span,
) -> core.Expr {
  let core_fields =
    list.map(args, fn(named_arg) {
      let #(name, arg) = named_arg
      #(name, expr(arg))
    })
  let core_tail = option.map(tail, expr)
  // TODO: span.merge(first_span, last_span)
  core.rcd_values(core_fields, core_tail, span)
}

fn arguments_pat(
  args: List(#(String, tao.Pattern)),
  opt_tail: Option(Pattern),
  span: Span,
) -> core.Pattern {
  let core_fields =
    list.index_map(args, fn(named_arg, index) {
      let #(_, arg) = named_arg
      #(int.to_string(index + 1), pattern(arg))
    })
  let core_tail = option.map(opt_tail, pattern)
  // TODO: span.merge(first_span, last_span)
  core.prcd(core_fields, core_tail, span)
}

fn function(
  opt_fun_name: Option(String),
  implicits: List(tao.Param),
  implicits_tail: Option(tao.Type),
  params: List(tao.Param),
  params_tail: Option(tao.Type),
  opt_returns: Option(tao.Type),
  body: tao.Expr,
  span: Span,
) -> core.Expr {
  case implicits {
    [] -> {
      let param_name = "$args"
      // TODO: infer span from args
      let args_span = span
      let param_fields =
        list.index_map(params, fn(param, index) {
          let #(_, #(opt_type, opt_default)) = param
          let core_type = opt_expr(opt_type)
          let core_default = opt_expr(opt_default)
          #(int.to_string(index + 1), #(core_type, core_default))
        })
      let core_params_tail = opt_expr(params_tail)
      let core_param_type = core.rcd(param_fields, core_params_tail, args_span)
      let bindings =
        list.index_map(params, fn(param, index) {
          let #(p, _) = param
          #(int.to_string(index + 1), p)
        })
      let unpack = tao.Case(tao.prcd_strict(bindings, args_span), None, body)
      let match_expr = tao.match(tao.var(param_name, args_span), [unpack], span)
      let core_body = expr(match_expr)
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
  fun: tao.Expr,
  args: List(#(String, tao.Expr)),
  tail: Option(tao.Expr),
  span: Span,
) -> core.Expr {
  let core_fun = expr(fun)
  let core_args = arguments(args, tail, fun.span)
  core.Expr(core.App(core_fun, core_args), span)
}

fn case_list(cases: List(tao.Case)) -> List(core.Case) {
  list.map(cases, case_)
}

fn case_(c: tao.Case) -> core.Case {
  case c {
    tao.Case(pat, opt_guard, body) -> {
      let core_pat = pattern(pat)
      let core_guard = option.map(opt_guard, case_guard)
      let core_body = expr(body)
      core.Case(core_pat, core_guard, core_body)
    }
  }
}

fn case_guard(
  guard: #(tao.Expr, Option(tao.Pattern)),
) -> #(core.Expr, core.Pattern) {
  case guard {
    #(cond, None) -> {
      let cond = tao.ann(cond, tao.bool(cond.span), cond.span)
      let core_cond = expr(cond)
      let core_expect = core.pctr0("True", cond.span)
      #(core_cond, core_expect)
    }
    #(cond, Some(expect)) -> {
      let core_cond = expr(cond)
      let core_expect = pattern(expect)
      #(core_cond, core_expect)
    }
  }
}

pub fn pattern(p: Pattern) -> core.Pattern {
  case p.data {
    tao.PAny -> core.pany(p.span)
    tao.PVar(name) -> core.pvar(name, p.span)
    tao.PLit(l) -> core.Pattern(core.PLit(l), p.span)
    tao.PCtr("Int", [], None) -> core.pint_t(p.span)
    tao.PCtr("Float", [], None) -> core.pfloat_t(p.span)
    tao.PCtr("I8", [], None) -> core.pi8(p.span)
    // TODO: cover all LiteralType and Typ
    tao.PRcd(fields, tail) -> {
      let core_fields =
        list.map(fields, fn(field) {
          let #(name, p) = field
          #(name, pattern(p))
        })
      let core_tail = option.map(tail, pattern)
      core.prcd(core_fields, core_tail, p.span)
    }
    tao.PCtr(tag, args, tail) -> {
      let core_fields =
        list.map(args, fn(field) {
          let #(name, p) = field
          #(name, pattern(p))
        })
      let core_tail = option.map(tail, pattern)
      core.pctr(tag, core.prcd(core_fields, core_tail, p.span), p.span)
    }
  }
}

pub fn statement_list(
  block_ctx: BlockCtx,
  stmts: List(Stmt),
  return: core.Expr,
) -> core.Expr {
  case stmts {
    [] -> return
    [stmt, ..stmts] -> {
      let next = statement_list(block_ctx, stmts, return)
      statement(block_ctx, stmt, next)
    }
  }
}

pub fn statement(
  block_ctx: BlockCtx,
  stmt: Stmt,
  next: core.Expr,
) -> core.Expr {
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
      statement(block_ctx, stmt, next)
    }
    tao.Let(p, opt_type, value) -> {
      let core_pattern = pattern(p)
      let core_type = opt_expr(opt_type)
      let core_value = expr(value)
      core.let_pat(#(core_pattern, core_type, core_value), next, stmt.span)
    }
    tao.LetMut(name, opt_type, value) -> todo
    tao.Mut(name, value) -> todo
    tao.FnDef(
      name,
      implicits,
      implicits_tail,
      params,
      params_tail,
      returns,
      body,
    ) -> {
      let core_fn =
        function(
          Some(name),
          implicits,
          implicits_tail,
          params,
          params_tail,
          returns,
          body,
          stmt.span,
        )
      core.let_var(#(name, None, core_fn), next, stmt.span)
    }
    tao.FnOverload(name, choices) -> {
      let s = stmt.span
      let param1 = #("$type", Some(core.typ(0, s)))
      let match_body =
        list.map(choices, overload_choice(_, core.var("$args", s)))
        |> core.match(core.var("$type", s), _, s)
      let param2 = #("$args", Some(core.var("$type", s)))
      let core_expr = core.lam(param2, match_body, s)
      let core_expr = core.for(param1, core_expr, s)
      core.let_var(#(name, None, core_expr), next, s)
    }
    tao.Test(name, arg, expect) -> {
      let core_arg = expr(arg)
      let core_cases = [
        core.Case(
          pattern(expect),
          None,
          core.ctr("Pass", core.rcd([], None, arg.span), arg.span),
        ),
        core.Case(
          core.pvar("got", arg.span),
          None,
          core.ctr("Fail", core.var("got", arg.span), arg.span),
        ),
      ]
      let core_test = core.match(core_arg, core_cases, stmt.span)
      core.let_var(#(">>> " <> name, None, core_test), next, stmt.span)
    }
    tao.TypeDef(type_def) -> todo
    tao.For(iterator, range, body) -> todo
    tao.While(condition, body) -> todo
    tao.Return(ret_expr) -> expr(ret_expr)
    tao.Break -> todo
    tao.Continue -> todo
  }
}

fn overload_choice(
  choice: tao.OverloadChoice,
  core_arg: core.Expr,
) -> core.Case {
  let tao.OverloadChoice(opt_mod_name, name, args, opt_guard, s) = choice
  let core_pat = arguments_pat(args, None, s)
  let core_guard = option.map(opt_guard, case_guard)
  let core_body_fun = case opt_mod_name {
    Some(mod_name) -> core.dot(core.var(mod_name, s), name, s)
    None -> core.var(name, s)
  }
  let core_body = core.app(core_body_fun, core_arg, s)
  core.Case(core_pat, core_guard, core_body)
}

fn rcd_fields(
  fields: List(#(String, Option(tao.Expr))),
) -> List(#(String, core.Expr)) {
  let s = Span("", 0, 0, 0, 0)
  list.map(fields, fn(f) {
    let #(name, opt_arg) = f
    let core_arg = case opt_arg {
      Some(arg) -> expr(arg)
      // TODO: get span from name
      None -> core.var(name, s)
    }
    #(name, core_arg)
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
