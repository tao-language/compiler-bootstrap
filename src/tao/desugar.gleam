import core/ast as core
import core/format
import filepath
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/regexp
import gleam/result
import gleam/string
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

pub fn module(
  defs: List(#(String, List(String))),
  exports: List(String),
  mod: Module,
) -> core.Expr {
  let #(mod_name, stmts) = mod
  let span = Span(mod_name, 0, 0, 0, 0)
  let return_expr = core.rcd_vars(exports, None, span)
  statement_list(defs, new_block_ctx, stmts, return_expr)
}

pub fn expr(defs: List(#(String, List(String))), e: tao.Expr) -> core.Expr {
  case e.data {
    tao.Hole(id) -> core.hole(id, e.span)
    tao.Lit(value) -> core.lit(value, e.span)
    tao.Var(name) -> core.var(name, e.span)
    tao.Ctr("Int", [], None) -> core.int_t(e.span)
    tao.Ctr("Float", [], None) -> core.float_t(e.span)
    tao.Ctr(tag, args, tail) -> {
      let core_args = arguments(defs, args, tail, e.span)
      core.ctr(tag, core_args, e.span)
    }
    tao.Rcd(fields, tail) -> {
      let core_fields = rcd_fields(defs, fields)
      let core_tail = opt_expr(defs, tail)
      core.rcd_values(core_fields, core_tail, e.span)
    }
    tao.RcdT(fields, tail) -> {
      let core_fields = rcdt_fields(defs, fields)
      let core_tail = opt_expr(defs, tail)
      core.rcd(core_fields, core_tail, e.span)
    }
    tao.Ann(value, type_) -> {
      let core_value = expr(defs, value)
      let core_type = expr(defs, type_)
      core.ann(core_value, core_type, e.span)
    }
    tao.Fn(implicits, implicits_tail, params, params_tail, returns, body) ->
      function(
        defs,
        None,
        implicits,
        implicits_tail,
        params,
        params_tail,
        returns,
        body,
        e.span,
        Some("fn <anonymous>"),
      )
    tao.FnT(implicits, params, body) ->
      function_type(defs, implicits, params, body, e.span)
    tao.App(fun, args, tail) -> application(defs, fun, args, tail, e.span)
    tao.Match(arg, cases) -> {
      let core_arg = expr(defs, arg)
      let core_cases = case_list(defs, cases)
      core.match(core_arg, core_cases, e.span)
    }
    tao.Op1(op, expr) -> {
      echo e.data
      todo
    }
    tao.Op2(op, lhs, rhs) -> {
      let op_name = tao.binop_name(op)
      let fun = tao.var(op_name, e.span)
      let args = [#("", lhs), #("", rhs)]
      expr(defs, tao.app(fun, args, e.span))
    }
    tao.Call(name, args) -> {
      let fields =
        list.map(args, fn(arg) {
          let #(name, value) = arg
          #(name, Some(value))
        })
      let core_arg = expr(defs, tao.rcd(fields, None, e.span))
      core.call(name, core_arg, e.span)
    }
    tao.Do(block) -> {
      let return = core.rcd([], None, e.span)
      statement_list(defs, new_block_ctx, block, return)
    }
    tao.Err -> core.err(e.span)
  }
}

fn opt_expr(
  defs: List(#(String, List(String))),
  opt_expr: Option(tao.Expr),
) -> Option(core.Expr) {
  option.map(opt_expr, expr(defs, _))
}

fn arguments(
  defs: List(#(String, List(String))),
  args: List(#(String, tao.Expr)),
  tail: Option(tao.Expr),
  span: Span,
) -> core.Expr {
  let core_fields =
    list.map(args, fn(named_arg) {
      let #(name, arg) = named_arg
      #(name, expr(defs, arg))
    })
  let core_tail = option.map(tail, expr(defs, _))
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
  defs: List(#(String, List(String))),
  opt_fun_name: Option(String),
  implicits: List(tao.Param),
  implicits_tail: Option(tao.Type),
  params: List(tao.Param),
  params_tail: Option(tao.Type),
  opt_returns: Option(tao.Type),
  body: tao.Expr,
  span: Span,
  trace: Option(String),
) -> core.Expr {
  case implicits {
    [] -> {
      let param_name = "$args"
      // TODO: infer span from args
      let args_span = span
      let param_fields =
        list.index_map(params, fn(param, index) {
          let #(_, #(opt_type, opt_default)) = param
          let core_type = opt_expr(defs, opt_type)
          let core_default = opt_expr(defs, opt_default)
          #(int.to_string(index + 1), #(core_type, core_default))
        })
      let core_params_tail = opt_expr(defs, params_tail)
      let core_param_type = core.rcd(param_fields, core_params_tail, args_span)
      let bindings =
        list.index_map(params, fn(param, index) {
          let #(p, _) = param
          #(int.to_string(index + 1), p)
        })
      let unpack = tao.Case(tao.prcd_strict(bindings, args_span), None, body)
      let match_expr = tao.match(tao.var(param_name, args_span), [unpack], span)
      let core_body = expr(defs, match_expr)
      let core_body = case opt_returns {
        None -> core_body
        Some(returns) -> {
          let core_body_type = expr(defs, returns)
          core.ann(core_body, core_body_type, returns.span)
        }
      }
      let core_fun =
        core.Expr(
          core.Lam(#(param_name, Some(core_param_type)), core_body),
          span,
          trace,
        )
      case opt_fun_name {
        Some(fun_name) -> core.fix(fun_name, core_fun, span)
        None -> core_fun
      }
    }
    _ -> todo
  }
}

fn function_type(
  defs: List(#(String, List(String))),
  implicits: List(tao.Param),
  params: List(tao.Param),
  body: tao.Expr,
  span: Span,
) -> core.Expr {
  todo
}

fn application(
  defs: List(#(String, List(String))),
  fun: tao.Expr,
  args: List(#(String, tao.Expr)),
  tail: Option(tao.Expr),
  span: Span,
) -> core.Expr {
  let core_fun = expr(defs, fun)
  let core_args = arguments(defs, args, tail, fun.span)
  core.app(core_fun, core_args, span)
}

fn case_list(
  defs: List(#(String, List(String))),
  cases: List(tao.Case),
) -> List(core.Case) {
  list.map(cases, case_(defs, _))
}

fn case_(defs: List(#(String, List(String))), c: tao.Case) -> core.Case {
  case c {
    tao.Case(pat, opt_guard, body) -> {
      let core_pat = pattern(pat)
      let core_guard = option.map(opt_guard, case_guard(defs, _))
      let core_body = expr(defs, body)
      core.Case(core_pat, core_guard, core_body)
    }
  }
}

fn case_guard(
  defs: List(#(String, List(String))),
  guard: #(tao.Expr, Option(tao.Pattern)),
) -> #(core.Expr, core.Pattern) {
  case guard {
    #(cond, None) -> {
      let cond = tao.ann(cond, tao.bool(cond.span), cond.span)
      let core_cond = expr(defs, cond)
      let core_expect = core.pctr0("True", cond.span)
      #(core_cond, core_expect)
    }
    #(cond, Some(expect)) -> {
      let core_cond = expr(defs, cond)
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
  defs: List(#(String, List(String))),
  block_ctx: BlockCtx,
  stmts: List(Stmt),
  return: core.Expr,
) -> core.Expr {
  case stmts {
    [] -> return
    [stmt, ..stmts] -> {
      let next = statement_list(defs, block_ctx, stmts, return)
      statement(defs, block_ctx, stmt, next)
    }
  }
}

pub fn statement(
  defs: List(#(String, List(String))),
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
      let mod_name = "/" <> path
      let def = #(alias, None, core.var(mod_name, stmt.span))
      core.let_var_trace(def, next, stmt.span, Some("import " <> path))
    }
    tao.Import(path, opt_alias, [#(name, opt_name_alias), ..names]) -> {
      let stmt = tao.import_(path, opt_alias, names, stmt.span)
      let name_alias = case opt_name_alias {
        Some(alias) -> alias
        None -> name
      }
      let mod_name = "/" <> path
      let access = core.dot(core.var(mod_name, stmt.span), name, stmt.span)
      let next = core.let_var(#(name_alias, None, access), next, stmt.span)
      statement(defs, block_ctx, stmt, next)
    }
    tao.ImportAll(path, opt_alias) -> {
      let mod_name = "/" <> path
      let names =
        list.key_find(defs, mod_name)
        |> result.unwrap([])
        |> list.filter(is_public_name)
        |> list.map(fn(x) { #(x, None) })
      let stmt = tao.Stmt(tao.Import(path, opt_alias, names), stmt.span)
      statement(defs, block_ctx, stmt, next)
    }
    tao.Let(p, opt_type, value) -> {
      let core_pattern = pattern(p)
      let core_type = opt_expr(defs, opt_type)
      let core_value = expr(defs, value)
      core.let_pat_trace(
        #(core_pattern, core_type, core_value),
        next,
        stmt.span,
        Some("let " <> format.pattern(core_pattern, 80, 2)),
      )
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
          defs,
          Some(name),
          implicits,
          implicits_tail,
          params,
          params_tail,
          returns,
          body,
          stmt.span,
          Some("fn " <> name),
        )
      core.let_var(#(name, None, core_fn), next, stmt.span)
    }
    tao.FnOverload(name, choices) -> {
      let s = stmt.span
      let param1 = #("$type", Some(core.typ(0, s)))
      let match_body =
        list.map(choices, overload_choice(defs, _, core.var("$args", s)))
        |> core.match(core.var("$type", s), _, s)
      let param2 = #("$args", Some(core.var("$type", s)))
      let core_expr = core.lam(param2, match_body, s)
      let core_expr = core.for(param1, core_expr, s)
      core.let_var_trace(#(name, None, core_expr), next, s, Some("fn " <> name))
    }
    tao.Test(name, arg, expect) -> {
      let core_arg = expr(defs, arg)
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
      core.let_var_trace(
        #(">>> " <> name, None, core_test),
        next,
        stmt.span,
        Some(">>> " <> name),
      )
    }
    tao.TypeDef(type_def) -> todo
    tao.For(iterator, range, body) -> todo
    tao.While(condition, body) -> todo
    tao.Return(ret_expr) -> expr(defs, ret_expr)
    tao.Break -> todo
    tao.Continue -> todo
  }
}

fn is_public_name(name: String) -> Bool {
  case name {
    "_" <> _ -> False
    ">>> " <> _ -> False
    _ -> True
  }
}

fn overload_choice(
  defs: List(#(String, List(String))),
  choice: tao.OverloadChoice,
  core_arg: core.Expr,
) -> core.Case {
  let tao.OverloadChoice(fun, args, opt_guard, s) = choice
  let core_pat = arguments_pat(args, None, s)
  let core_guard = option.map(opt_guard, case_guard(defs, _))
  let core_body = case fun {
    tao.OverloadVar(name) -> {
      let core_fun = core.var(name, s)
      core.app(core_fun, core_arg, s)
    }
    tao.OverloadCall(name) -> core.call(name, core_arg, s)
    tao.OverloadDot(name, field) -> {
      let core_fun = core.dot(core.var(name, s), field, s)
      core.app(core_fun, core_arg, s)
    }
  }
  core.Case(core_pat, core_guard, core_body)
}

fn rcd_fields(
  defs: List(#(String, List(String))),
  fields: List(#(String, Option(tao.Expr))),
) -> List(#(String, core.Expr)) {
  let s = Span("", 0, 0, 0, 0)
  list.map(fields, fn(f) {
    let #(name, opt_arg) = f
    let core_arg = case opt_arg {
      Some(arg) -> expr(defs, arg)
      // TODO: get span from name
      None -> core.var(name, s)
    }
    #(name, core_arg)
  })
}

fn rcdt_fields(
  defs: List(#(String, List(String))),
  fields: List(#(String, #(Option(tao.Type), Option(tao.Expr)))),
) -> List(#(String, #(Option(core.Type), Option(core.Expr)))) {
  list.map(fields, fn(f) {
    let #(name, #(type_, default_)) = f
    let type_term = case type_ {
      None -> None
      Some(t) -> Some(expr(defs, t))
    }
    let default_term = case default_ {
      None -> None
      Some(e) -> Some(expr(defs, e))
    }
    #(name, #(type_term, default_term))
  })
}

fn to_valid_var(name: String) -> String {
  let name = name |> string.replace("-", "_") |> string.replace(".", "_")
  case string.first(name) {
    Ok(first) ->
      case first {
        "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" -> "_" <> name
        _ -> name
      }
    _ -> name
  }
}
