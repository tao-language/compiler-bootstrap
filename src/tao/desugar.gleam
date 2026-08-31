import core/ast as core
import core/format
import core/literals as lit
import filepath
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/regexp
import gleam/result
import gleam/string
import syntax/span.{type Span, Span}
import tao/ast.{type Case, type Expr, type Module, type Pattern, type Stmt} as tao
import tao/declare.{is_public_name}

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
  exports: List(#(String, List(String))),
  mod: Module,
) -> core.Expr {
  let #(mod_name, stmts) = mod
  let span = Span(mod_name, 0, 0, 0, 0)
  let mod_exports = list.key_find(exports, mod_name) |> result.unwrap([])
  let return_expr = core.rcd_vars(mod_exports, None, span)
  statement_list(exports, new_block_ctx, stmts, return_expr)
}

pub fn expr(exports: List(#(String, List(String))), e: tao.Expr) -> core.Expr {
  case e.data {
    tao.Hole(id) -> core.hole_open(id, e.span)
    tao.Lit(value) -> core.lit(value, e.span)
    tao.Var(name) -> core.var(name, e.span)
    tao.Ctr("Type", [#(_, tao.Expr(tao.Lit(lit.Int(u)), _))], None) ->
      core.typ(u, e.span)
    tao.Ctr("Int", [], None) -> core.int_t(e.span)
    tao.Ctr("Float", [], None) -> core.float_t(e.span)
    tao.Ctr(tag, args, tail) -> {
      let core_args = arguments(exports, args, tail, e.span)
      core.ctr(tag, core_args, e.span)
    }
    tao.Rcd(fields, tail) -> {
      let core_fields = rcd_fields(exports, fields)
      let core_tail = opt_expr(exports, tail)
      core.rcd_values(core_fields, core_tail, e.span)
    }
    tao.RcdT(fields, tail) -> {
      let core_fields = rcdt_fields(exports, fields)
      let core_tail = opt_expr(exports, tail)
      core.rcd(core_fields, core_tail, e.span)
    }
    tao.Ann(value, type_) -> {
      let core_value = expr(exports, value)
      let core_type = expr(exports, type_)
      core.ann(core_value, core_type, e.span)
    }
    tao.Fn(opt_name, implicits, params, returns, body) ->
      function(
        exports,
        opt_name,
        implicits,
        params,
        returns,
        body,
        e.span,
        Some("fn <anonymous>"),
      )
    tao.FnT(implicits, params, body) ->
      function_type(exports, implicits, params, body, e.span)
    tao.App(fun, args, tail) -> application(exports, fun, args, tail, e.span)
    tao.Match(arg, cases) -> {
      let core_arg = expr(exports, arg)
      let core_cases = case_list(exports, cases)
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
      expr(exports, tao.app(fun, args, e.span))
    }
    tao.Do(block) -> {
      let return = core.rcd([], None, e.span)
      statement_list(exports, new_block_ctx, block, return)
    }
    tao.Err -> core.err(e.span)
  }
}

fn opt_expr(
  exports: List(#(String, List(String))),
  opt_expr: Option(tao.Expr),
) -> Option(core.Expr) {
  option.map(opt_expr, expr(exports, _))
}

fn arguments(
  exports: List(#(String, List(String))),
  args: List(#(String, tao.Expr)),
  tail: Option(tao.Expr),
  span: Span,
) -> core.Expr {
  let core_fields =
    list.map(args, fn(named_arg) {
      let #(name, arg) = named_arg
      #(name, expr(exports, arg))
    })
  let core_tail = option.map(tail, expr(exports, _))
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

fn parameters_type(
  exports: List(#(String, List(String))),
  params: tao.Parameters,
  span: Span,
) -> core.Type {
  let #(args, tail) = params
  let param_fields =
    list.index_map(args, fn(param, index) {
      let #(_, #(opt_type, opt_default)) = param
      let core_type = opt_expr(exports, opt_type)
      let core_default = opt_expr(exports, opt_default)
      #(int.to_string(index + 1), #(core_type, core_default))
    })
  let core_params_tail = opt_expr(exports, tail)
  core.rcd(param_fields, core_params_tail, span)
}

fn parameters_unpack(
  exports: List(#(String, List(String))),
  var_name: String,
  params: tao.Parameters,
  body: tao.Expr,
  span: Span,
) -> core.Expr {
  let #(args, tail) = params
  let bindings =
    list.index_map(args, fn(param, index) {
      let #(p, _) = param
      #(int.to_string(index + 1), p)
    })
  let cases = [tao.Case(tao.prcd_strict(bindings, span), None, body)]
  let match_expr = tao.match(tao.var(var_name, span), cases, span)
  expr(exports, match_expr)
}

fn function(
  exports: List(#(String, List(String))),
  opt_fun_name: Option(String),
  implicits: tao.Parameters,
  params: tao.Parameters,
  opt_returns: Option(tao.Type),
  body: tao.Expr,
  span: Span,
  trace: Option(String),
) -> core.Expr {
  case implicits {
    #([], None) -> {
      let param_name = "__args"
      // TODO: infer span from args
      let args_span = span
      let core_param_type = parameters_type(exports, params, args_span)
      let core_body =
        parameters_unpack(exports, param_name, params, body, args_span)
      let core_body = case opt_returns {
        None -> core_body
        Some(returns) -> {
          let core_body_type = expr(exports, returns)
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
  exports: List(#(String, List(String))),
  implicits: tao.Parameters,
  params: tao.Parameters,
  returns: tao.Type,
  span: Span,
) -> core.Expr {
  case implicits {
    #([], None) -> {
      let name = "__args"
      let core_param_type = parameters_type(exports, params, span)
      let core_returns = parameters_unpack(exports, name, params, returns, span)
      core.pi(#(name, Some(core_param_type)), core_returns, span)
    }
    _ -> {
      let name = "__impl"
      let core_implicits_type = parameters_type(exports, implicits, span)
      let body = tao.fn_t(#([], None), params, returns, span)
      let core_body = parameters_unpack(exports, name, implicits, body, span)
      core.for(#(name, Some(core_implicits_type)), core_body, span)
    }
  }
}

fn application(
  exports: List(#(String, List(String))),
  fun: tao.Expr,
  args: List(#(String, tao.Expr)),
  tail: Option(tao.Expr),
  span: Span,
) -> core.Expr {
  let core_fun = expr(exports, fun)
  let core_args = arguments(exports, args, tail, fun.span)
  core.app(core_fun, core_args, span)
}

fn case_list(
  exports: List(#(String, List(String))),
  cases: List(tao.Case),
) -> List(core.Case) {
  list.map(cases, case_(exports, _))
}

fn case_(exports: List(#(String, List(String))), c: tao.Case) -> core.Case {
  case c {
    tao.Case(pat, opt_guard, body) -> {
      let core_pat = pattern(pat)
      let core_guard = option.map(opt_guard, case_guard(exports, _))
      let core_body = expr(exports, body)
      core.Case(core_pat, core_guard, core_body)
    }
  }
}

fn case_guard(
  exports: List(#(String, List(String))),
  guard: #(tao.Expr, Option(tao.Pattern)),
) -> #(core.Expr, core.Pattern) {
  case guard {
    #(cond, None) -> {
      let cond = tao.ann(cond, tao.bool(cond.span), cond.span)
      let core_cond = expr(exports, cond)
      let core_expect = core.pctr0("True", cond.span)
      #(core_cond, core_expect)
    }
    #(cond, Some(expect)) -> {
      let core_cond = expr(exports, cond)
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
    tao.PCtr("Type", [#(_, tao.Pattern(tao.PLit(lit.Int(u)), _))], None) ->
      core.ptyp(u, p.span)
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
  exports: List(#(String, List(String))),
  block_ctx: BlockCtx,
  stmts: List(Stmt),
  return: core.Expr,
) -> core.Expr {
  case stmts {
    [] -> return
    [stmt, ..stmts] -> {
      let next = statement_list(exports, block_ctx, stmts, return)
      statement(exports, block_ctx, stmt, next)
    }
  }
}

pub fn statement(
  exports: List(#(String, List(String))),
  block_ctx: BlockCtx,
  stmt: Stmt,
  next: core.Expr,
) -> core.Expr {
  let s = stmt.span
  case stmt.data {
    tao.Import(path, alias, tao.ImportAll) -> {
      let mod_name = path
      let scope =
        list.key_find(exports, mod_name)
        |> result.unwrap([])
        |> list.filter(is_public_name)
        |> list.map(fn(x) { #(x, x) })
        |> tao.ImportSome
      let stmt = tao.Stmt(tao.Import(path, alias, scope), s)
      statement(exports, block_ctx, stmt, next)
    }
    tao.Import(path, alias, tao.ImportSome(names)) -> {
      let mod_name = path
      case names {
        [] -> {
          let def = #(alias, None, core.var(mod_name, s))
          core.let_var_trace(def, next, s, Some("import " <> path))
        }
        [#(x, y), ..names] -> {
          let stmt = tao.import_some(path, alias, names, s)
          let access = core.dot(core.var(mod_name, s), x, s)
          let trace = Some("import " <> path <> " {" <> x <> "}")
          let next = core.let_var_trace(#(y, None, access), next, s, trace)
          statement(exports, block_ctx, stmt, next)
        }
      }
    }
    tao.Extern(name, args, ret) -> {
      let core_args =
        list.index_map(args, fn(arg, index) {
          let name = int.to_string(index + 1)
          #(name, expr(exports, arg))
        })
      let core_ret = expr(exports, ret)
      let core_value =
        core.lam(
          #("__args", Some(core.rcd_values(core_args, None, s))),
          core.call(name, core_ret, core.var("__args", s), s),
          s,
        )
      core.let_var_trace(
        #(name, None, core_value),
        next,
        s,
        Some("extern " <> name),
      )
    }
    tao.LetVar(name, opt_type, value) -> {
      let core_type = opt_expr(exports, opt_type)
      let core_value = expr(exports, value)
      core.let_var_trace(
        #(name, core_type, core_value),
        next,
        s,
        Some("let-var " <> name),
      )
    }
    tao.LetPat(pattern, types, value) -> {
      // core.let_pat_trace(
      //   #(core_pattern, core_types, core_value),
      //   next,
      //   s,
      //   Some("let " <> format.pattern(core_pattern, 80, 2)),
      // )
      todo
    }
    tao.LetMut(name, opt_type, value) -> todo
    tao.Mut(name, value) -> todo
    tao.FnDef(name, implicits, params, returns, body) -> {
      let core_fn =
        function(
          exports,
          Some(name),
          implicits,
          params,
          returns,
          body,
          s,
          Some("fn " <> name),
        )
      core.let_var(#(name, None, core_fn), next, s)
    }
    tao.FnOverload(name, choices) -> {
      let param1 = #("__type", Some(core.typ(0, s)))
      let match_body =
        list.map(choices, overload_choice(exports, _, core.var("__args", s)))
        |> core.match(core.var("__type", s), _, s)
      let param2 = #("__args", Some(core.var("__type", s)))
      let core_expr = core.for(param1, core.lam(param2, match_body, s), s)
      core.let_var_trace(#(name, None, core_expr), next, s, Some("fn " <> name))
    }
    tao.Test(name, arg, expect) -> {
      let core_arg = expr(exports, arg)
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
      let core_test = core.match(core_arg, core_cases, s)
      core.let_var_trace(#(name, None, core_test), next, s, Some(name))
    }
    tao.TypeDef(type_def) -> todo
    tao.For(iterator, range, body) -> todo
    tao.While(condition, body) -> todo
    tao.Return(ret_expr) -> expr(exports, ret_expr)
    tao.Break -> todo
    tao.Continue -> todo
  }
}

fn overload_choice(
  exports: List(#(String, List(String))),
  choice: tao.OverloadChoice,
  core_arg: core.Expr,
) -> core.Case {
  let s = choice.span
  let core_pat = arguments_pat(choice.args, None, s)
  let core_guard = option.map(choice.guard, case_guard(exports, _))
  let core_fun = case choice.mod_name {
    Some(mod_name) -> core.dot(core.var(mod_name, s), choice.name, s)
    None -> core.var(choice.name, s)
  }
  let core_body = core.app(core_fun, core_arg, s)
  core.Case(core_pat, core_guard, core_body)
}

fn rcd_fields(
  exports: List(#(String, List(String))),
  fields: List(#(String, Option(tao.Expr))),
) -> List(#(String, core.Expr)) {
  let s = Span("", 0, 0, 0, 0)
  list.map(fields, fn(f) {
    let #(name, opt_arg) = f
    let core_arg = case opt_arg {
      Some(arg) -> expr(exports, arg)
      // TODO: get span from name
      None -> core.var(name, s)
    }
    #(name, core_arg)
  })
}

fn rcdt_fields(
  exports: List(#(String, List(String))),
  fields: List(#(String, #(Option(tao.Type), Option(tao.Expr)))),
) -> List(#(String, #(Option(core.Type), Option(core.Expr)))) {
  list.map(fields, fn(f) {
    let #(name, #(type_, default_)) = f
    let type_term = case type_ {
      None -> None
      Some(t) -> Some(expr(exports, t))
    }
    let default_term = case default_ {
      None -> None
      Some(e) -> Some(expr(exports, e))
    }
    #(name, #(type_term, default_term))
  })
}
