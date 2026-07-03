/// Type Inference — Bidirectional Type Checking
///
/// The `infer` module implements bidirectional type checking for the Core
/// language. Every term can be synthesized (inferred), and `check` is a
/// thin wrapper that synthesizes the term then unifies its type with
/// the expected type.
import core/ast.{type Expr}
import core/coerce.{coerce}
import core/context.{type Context}
import core/error as e
import core/eval.{eval}
import core/format
import core/literals.{type Literal, type LiteralType} as lit
import core/quote.{quote}
import core/term.{type Term} as tm
import core/unify.{unify}
import core/unwrap.{unwrap, unwrap_term}
import core/value.{type Type, type Value} as v
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import syntax/span.{type Span, Span}

/// Infer the type of a term (synthesis).
///
/// Returns #(result_term, type_value, ctx) where:
/// - result_term is the original term with holes filled and implicit args expanded
/// - type_value is the inferred type (a Value)
/// - ctx is the updated ctx with any new bindings
pub fn infer(ctx: Context, term_ast: ast.Expr) -> #(Term, Value, Context) {
  case term_ast.data {
    ast.Typ(level) -> infer_typ(ctx, level)
    ast.Hole(id) -> infer_hole(ctx, id)
    ast.Lit(value) -> infer_lit(ctx, value)
    ast.LitT(t) -> infer_litt(ctx, t)
    ast.Var(name) -> infer_var(ctx, name, term_ast.span)
    ast.Ctr(tag, arg) -> infer_ctr(ctx, tag, arg)
    ast.Rcd(fields, tail) -> infer_rcd(ctx, fields, tail)
    ast.Call(name, returns, args) -> infer_call(ctx, name, returns, args)
    ast.Ann(inner, type_) -> infer_ann(ctx, inner, type_)
    ast.Lam(implicit, param, body) -> infer_lam(ctx, implicit, param, body)
    ast.Pi(implicit, param, body) -> infer_pi(ctx, implicit, param, body)
    ast.Fix(name, body) -> infer_fix(ctx, name, body, term_ast.span)
    ast.App(implicit, fun, arg) ->
      infer_app(ctx, implicit, fun, arg, term_ast.span)
    ast.Match(arg, cases) -> infer_match(ctx, arg, cases)
    // ast.TypeDef(params, constructors) ->
    //   infer_type_def(ctx, params, constructors, term_ast.span)
    ast.Err -> infer_err(ctx)
    x -> {
      let msg = string.inspect(x)
      todo as msg
    }
  }
}

/// Check that a term has the expected type (verification).
///
/// This is a thin wrapper: infer the term, then fill in any missing
/// record defaults at the value level before unifying.
pub fn check(
  ctx: Context,
  ast: Expr,
  expected: #(Value, Span),
) -> #(Term, Value, Context) {
  let #(expected_type, type_span) = expected
  let #(term, inferred_type, ctx) = infer(ctx, ast)
  let term = unwrap_term(ctx.ffi, ctx.subst, ctx.env, term)
  let expected_type = unwrap(ctx.ffi, ctx.subst, expected_type)
  let term = coerce(term, expected_type)
  case term, expected_type {
    tm.Hole(_), _ -> #(term, expected_type, ctx)
    tm.Lit(lit.Int(_)), v.LitT(ty)
      if ty == lit.I8
      || ty == lit.I16
      || ty == lit.I32
      || ty == lit.I64
      || ty == lit.U8
      || ty == lit.U16
      || ty == lit.U32
      || ty == lit.U64
    -> #(term, expected_type, ctx)
    tm.Lit(lit.Int(k)), v.LitT(ty)
      if ty == lit.FloatT || ty == lit.F16 || ty == lit.F32 || ty == lit.F64
    -> #(tm.float(int.to_float(k)), expected_type, ctx)
    tm.Lit(lit.Float(_)), v.LitT(ty)
      if ty == lit.FloatT || ty == lit.F16 || ty == lit.F32 || ty == lit.F64
    -> #(term, expected_type, ctx)
    _, _ -> {
      let ctx =
        unify(ctx, #(inferred_type, ast.span), #(expected_type, type_span))
      let expected_type = unwrap(ctx.ffi, ctx.subst, expected_type)
      #(term, expected_type, ctx)
    }
  }
}

fn check_on_ast(
  ctx: Context,
  ast: Expr,
  type_: Expr,
) -> #(Term, #(Term, Value), Context) {
  let #(type_term, _, ctx) = infer(ctx, type_)
  let type_val = eval(ctx.ffi, ctx.env, type_term)
  let #(term, type_val, ctx) = check(ctx, ast, #(type_val, type_.span))
  #(term, #(type_term, type_val), ctx)
}

fn infer_typ(ctx: Context, level: Int) -> #(Term, Value, Context) {
  #(tm.Typ(level), v.Typ(level + 1), ctx)
}

fn infer_hole(ctx: Context, id: Option(Int)) -> #(Term, Value, Context) {
  case id {
    Some(hole_id) -> {
      // Concrete hole, create a new hole for its type.
      let #(type_id, ctx) = context.new_hole(ctx)
      #(tm.Hole(hole_id), v.hole(type_id), ctx)
    }
    None -> {
      // Unknown hole, instantiate a fresh new hole.
      let #(id, ctx) = context.new_hole(ctx)
      infer_hole(ctx, Some(id))
    }
  }
}

fn infer_lit(ctx: Context, value: Literal) -> #(Term, Value, Context) {
  let type_ = case value {
    lit.Int(_) -> v.int_t
    lit.Float(_) -> v.float_t
  }
  #(tm.Lit(value), type_, ctx)
}

fn infer_litt(ctx: Context, value: LiteralType) -> #(Term, Value, Context) {
  #(tm.LitT(value), v.Typ(0), ctx)
}

fn infer_var(
  ctx: Context,
  name: String,
  span: Span,
) -> #(Term, Value, Context) {
  case context.lookup(ctx, name) {
    Some(#(index, type_)) -> #(tm.Var(index), type_, ctx)
    None -> {
      let ctx = context.with_err(ctx, e.VarUndefined(name, span))
      #(tm.Err, v.Err, ctx)
    }
  }
}

fn infer_ctr(ctx: Context, tag: String, arg: Expr) -> #(Term, Value, Context) {
  let #(arg, arg_type, ctx) = infer(ctx, arg)
  #(tm.Ctr(tag, arg), v.Ctr(tag, arg_type), ctx)
}

fn infer_rcd(
  ctx: Context,
  fields: List(#(String, #(Option(Expr), Option(Expr)))),
  tail: Option(Expr),
) -> #(Term, Value, Context) {
  let #(fields, field_types, ctx) = infer_rcd_fields(ctx, fields)
  let #(tail, tail_type, ctx) = case tail {
    None -> #(None, None, ctx)
    Some(tail) -> {
      let #(tail, tail_type, ctx) = infer(ctx, tail)
      #(Some(tail), Some(tail_type), ctx)
    }
  }
  #(tm.rcd_open(fields, tail), v.rcd_open(field_types, tail_type), ctx)
}

fn infer_rcd_fields(
  ctx: Context,
  fields: List(#(String, #(Option(Expr), Option(Expr)))),
) -> #(List(#(String, Term)), List(#(String, Type)), Context) {
  let s = Span("", 0, 0, 0, 0)
  case fields {
    [] -> #([], [], ctx)
    [#(name, #(opt_term, _)), ..fields] -> {
      let #(term, ctx) = case opt_term {
        Some(term) -> #(term, ctx)
        None -> {
          let #(id, ctx) = context.new_hole(ctx)
          // TODO: get span from field name
          #(ast.hole(Some(id), s), ctx)
        }
      }
      let #(term, type_, ctx) = infer(ctx, term)
      let #(fields, field_types, ctx) = infer_rcd_fields(ctx, fields)
      #([#(name, term), ..fields], [#(name, type_), ..field_types], ctx)
    }
  }
}

fn infer_call(
  ctx: Context,
  name: String,
  returns_ast: Expr,
  args: List(Expr),
) -> #(Term, Value, Context) {
  let #(args, ctx) = check_call_args(ctx, args)
  let #(returns, _, ctx) = infer(ctx, returns_ast)
  let returns_val = eval(ctx.ffi, ctx.env, returns)
  let returns_val = unwrap(ctx.ffi, ctx.subst, returns_val)
  #(tm.Call(name, returns, args), returns_val, ctx)
}

fn check_call_args(ctx: Context, args: List(Expr)) -> #(List(Term), Context) {
  case args {
    [] -> #([], ctx)
    [arg, ..args] -> {
      let #(arg, _, ctx) = infer(ctx, arg)
      let #(args, ctx) = check_call_args(ctx, args)
      #([arg, ..args], ctx)
    }
  }
}

fn infer_ann(ctx: Context, ast: Expr, type_: Expr) -> #(Term, Value, Context) {
  let #(term, #(_, type_val), ctx) = check_on_ast(ctx, ast, type_)
  #(term, type_val, ctx)
}

fn infer_lam(
  ctx: Context,
  implicit: Bool,
  param: #(String, Option(ast.Type)),
  body: Expr,
) -> #(Term, Value, Context) {
  let #(name, opt_type_ast) = param
  let #(type_, ctx) = case opt_type_ast {
    Some(type_ast) -> {
      let #(param, _, ctx) = infer(ctx, type_ast)
      #(param, ctx)
    }
    None -> {
      let #(hole_id, ctx) = context.new_hole(ctx)
      #(tm.Hole(hole_id), ctx)
    }
  }
  let type_val = eval(ctx.ffi, ctx.env, type_)
  let level = list.length(ctx.env)
  let ctx = context.push_var(ctx, #(name, Some(v.var(level)), Some(type_val)))
  let #(body, body_type_val, ctx) = infer(ctx, body)
  let body_type_val = unwrap(ctx.ffi, ctx.subst, body_type_val)
  let body_type = quote(ctx.ffi, level + 1, body_type_val)
  let ctx = context.pop_vars(ctx, 1)
  let param_val = unwrap(ctx.ffi, ctx.subst, type_val)
  #(
    tm.Lam(implicit, #(name, type_), body),
    v.Pi(ctx.env, implicit, #(name, param_val), body_type),
    ctx,
  )
}

fn infer_pi(
  ctx: Context,
  implicit: Bool,
  param: ast.Param,
  body: Expr,
) -> #(Term, Value, Context) {
  let #(name, opt_type_ast) = param
  let #(type_, ctx) = case opt_type_ast {
    Some(type_ast) -> {
      let #(param, _, ctx) = infer(ctx, type_ast)
      #(param, ctx)
    }
    None -> {
      let #(hole_id, ctx) = context.new_hole(ctx)
      #(tm.Hole(hole_id), ctx)
    }
  }
  let type_val = eval(ctx.ffi, ctx.env, type_)
  let level = list.length(ctx.env)
  let ctx = context.push_var(ctx, #(name, Some(v.var(level)), Some(type_val)))
  let #(body, _, ctx) = infer(ctx, body)
  let ctx = context.pop_vars(ctx, 1)
  #(tm.Pi(implicit, #(name, type_), body), v.Typ(0), ctx)
}

fn infer_fix(
  ctx: Context,
  name: String,
  body: Expr,
  span: Span,
) -> #(Term, Value, Context) {
  let level = list.length(ctx.env)
  let #(hole_id, ctx) = context.new_hole(ctx)
  let type_hole = v.hole(hole_id)
  let ctx = context.push_var(ctx, #(name, Some(v.var(level)), Some(type_hole)))
  let #(body, body_type, ctx) = infer(ctx, body)
  let ctx = context.pop_vars(ctx, 1)
  let ctx = unify(ctx, #(type_hole, span), #(body_type, span))
  let body_type = unwrap(ctx.ffi, ctx.subst, body_type)
  #(tm.Fix(name, body), body_type, ctx)
}

fn infer_app(
  ctx: Context,
  app_implicit: Bool,
  fun_ast: Expr,
  arg_ast: Expr,
  span: Span,
) -> #(Term, Value, Context) {
  // Direct beta reduction: when the function is a syntactic lambda,
  // infer the argument FIRST to get its concrete value, then push
  // that concrete value (not a neutral variable) before inferring
  // the body. This is essential for dependent types where the body's
  // type depends on the argument's value.
  //
  // Only applies to explicit lambdas — implicit lambdas must go through
  // the normal path for implicit argument expansion.
  case fun_ast.data {
    ast.Lam(False, param, body) ->
      infer_beta_reduction(ctx, param, body, arg_ast, span)
    _ -> {
      let #(fun, fun_type, ctx) = infer(ctx, fun_ast)
      let fun_data = #(fun, fun_type, fun_ast.span)
      infer_app_args(ctx, app_implicit, fun_data, arg_ast, span)
    }
  }
}

/// Direct beta reduction: (%lam (x:T) => body)(arg)
fn infer_beta_reduction(
  ctx: Context,
  param: #(String, Option(ast.Type)),
  body: Expr,
  arg_ast: Expr,
  span: Span,
) -> #(Term, Value, Context) {
  let #(name, opt_type_ast) = param

  // Infer the parameter type
  let #(param_type, ctx) = case opt_type_ast {
    Some(type_ast) -> {
      let #(param, _, ctx) = infer(ctx, type_ast)
      #(param, ctx)
    }
    None -> {
      let #(hole_id, ctx) = context.new_hole(ctx)
      #(tm.Hole(hole_id), ctx)
    }
  }
  let param_type_val = eval(ctx.ffi, ctx.env, param_type)

  // Infer the argument FIRST, checking against the parameter type
  let #(arg, arg_type, ctx) = case opt_type_ast {
    Some(_) -> check(ctx, arg_ast, #(param_type_val, span))
    None -> infer(ctx, arg_ast)
  }

  // Get the concrete value of the argument
  let arg_val = eval(ctx.ffi, ctx.env, arg)

  // Push the CONCRETE value (not a neutral variable) to the context
  let level = list.length(ctx.env)
  let ctx = context.push_var(ctx, #(name, Some(arg_val), Some(arg_type)))

  // Infer the body with the concrete value in scope
  let #(body_term, body_type_val, ctx) = infer(ctx, body)
  let body_type_val = unwrap(ctx.ffi, ctx.subst, body_type_val)
  let body_type = quote(ctx.ffi, level + 1, body_type_val)

  // Pop the binding
  let ctx = context.pop_vars(ctx, 1)

  // Build the lambda and application terms
  let param_val = unwrap(ctx.ffi, ctx.subst, param_type_val)
  let arg_val_final = unwrap(ctx.ffi, ctx.subst, arg_val)
  let lam = tm.Lam(False, #(name, param_type), body_term)

  // Compute result type by applying the body type to the concrete argument
  let result_env = [arg_val_final, ..ctx.env]
  let result_type = eval(ctx.ffi, result_env, body_type)

  #(
    tm.App(False, lam, arg),
    unwrap(ctx.ffi, ctx.subst, result_type),
    ctx,
  )
}

fn infer_app_args(
  ctx: Context,
  app_implicit: Bool,
  fun_typed: #(Term, Value, Span),
  arg_ast: Expr,
  span: Span,
) -> #(Term, Value, Context) {
  let #(fun, fun_type, fun_span) = fun_typed
  case unwrap(ctx.ffi, ctx.subst, fun_type) {
    // Hole expansion
    v.Neut(v.NHole(id)) -> {
      let #(id, ctx) = case id >= 0 {
        True -> #(id, ctx)
        False -> context.new_hole(ctx)
      }
      let #(body_type_id, ctx) = context.new_hole(ctx)
      let #(arg, arg_type, ctx) = infer(ctx, arg_ast)
      let expected =
        v.Pi([], app_implicit, #("", arg_type), tm.Hole(body_type_id))
      let ctx = unify(ctx, #(v.hole(id), fun_span), #(expected, fun_span))
      let type_ = unwrap(ctx.ffi, ctx.subst, v.hole(body_type_id))
      #(tm.App(app_implicit, fun, arg), type_, ctx)
    }
    v.Neut(neut) -> {
      echo neut
      todo as "TODO: infer App on Neut function"
    }
    // Function application
    v.Pi(pi_env, pi_implicit, #(_, domain_val), codomain) ->
      case pi_implicit, app_implicit {
        // pi_implicit, app_implicit | pi_explicit, app_explicit
        True, True | False, False -> {
          // Matching implicit/explicit argument application
          // When implicit arg matches implicit param, the result is explicit
          // (the implicitness has been resolved)
          let #(arg, _, ctx) = check(ctx, arg_ast, #(domain_val, fun_span))
          let pi_env = [eval(ctx.ffi, ctx.env, arg), ..pi_env]
          let type_ = eval(ctx.ffi, pi_env, codomain)
          #(tm.App(False, fun, arg), unwrap(ctx.ffi, ctx.subst, type_), ctx)
        }
        // pi_implicit, app_explicit
        True, False as app_explicit -> {
          // Implicit argument expansion
          let #(hole_id, ctx) = context.new_hole(ctx)
          let fun = tm.App(False, fun, tm.Hole(hole_id))
          let pi_env = [v.hole(hole_id), ..pi_env]
          let fun_type = eval(ctx.ffi, pi_env, codomain)
          let fun_data = #(fun, fun_type, fun_span)
          infer_app_args(ctx, app_explicit, fun_data, arg_ast, span)
        }
        // pi_explicit, app_implicit
        False, True -> {
          // Expected explicit argument, got implicit argument instead
          // Still infer the arg to get as much additional information as possible in
          // the context, it might be solving holes for other parts of the program.
          let #(_, _, ctx) = infer(ctx, arg_ast)
          let error = e.AppExpectedExplicitArg(fun_type, span)
          #(tm.Err, v.Err, context.with_err(ctx, error))
        }
      }
    // Not a function type
    _ -> {
      // Still infer the arg to get as much additional information as possible in
      // the context, it might be solving holes for other parts of the program.
      let #(_, _, ctx) = infer(ctx, arg_ast)
      let error = e.NotAFunction(fun, fun_type, fun_span)
      #(tm.Err, v.Err, context.with_err(ctx, error))
    }
  }
}

fn infer_match(
  ctx: Context,
  arg_ast: Expr,
  cases_ast: List(ast.Case),
) -> #(Term, Value, Context) {
  let #(arg, arg_type, ctx) = infer(ctx, arg_ast)
  let #(cases, cases_type, ctx) =
    infer_match_case_list(ctx, #(arg_type, arg_ast.span), cases_ast)
  let arg_val = eval(ctx.ffi, ctx.env, arg)
  let value = eval.do_match(ctx.ffi, ctx.env, arg_val, cases)
  let type_ = eval.do_match(ctx.ffi, ctx.env, arg_val, cases_type)
  #(
    quote(ctx.ffi, list.length(ctx.env), value),
    unwrap(ctx.ffi, ctx.subst, type_),
    ctx,
  )
}

fn infer_match_case_list(
  ctx: Context,
  arg_type: #(Value, Span),
  cases_ast: List(ast.Case),
) -> #(List(tm.Case), List(tm.Case), Context) {
  case cases_ast {
    [] -> #([], [], ctx)
    [case_ast, ..cases_ast] -> {
      let #(case_, case_type, ctx) = infer_match_case(ctx, arg_type, case_ast)
      let #(cases, cases_types, ctx) =
        infer_match_case_list(ctx, arg_type, cases_ast)
      #([case_, ..cases], [case_type, ..cases_types], ctx)
    }
  }
}

fn infer_match_case(
  ctx: Context,
  arg_type: #(Value, Span),
  case_ast: ast.Case,
) -> #(tm.Case, tm.Case, Context) {
  let old_env_size = list.length(ctx.env)
  let #(pattern, ctx) = check_pattern(ctx, case_ast.pattern, arg_type)
  let #(guard, ctx) = bind_guard(ctx, case_ast.guard)
  let #(body, body_type_val, ctx) = infer(ctx, case_ast.body)
  let body_type = quote(ctx.ffi, list.length(ctx.env), body_type_val)
  let ctx = context.pop_vars(ctx, list.length(ctx.env) - old_env_size)
  #(tm.Case(pattern, guard, body), tm.Case(pattern, guard, body_type), ctx)
}

fn infer_pattern(
  ctx: Context,
  pattern_ast: ast.Pattern,
) -> #(tm.Pattern, Value, Context) {
  case pattern_ast.data {
    ast.PAny -> {
      let #(id, ctx) = context.new_hole(ctx)
      #(tm.PAny, v.hole(id), ctx)
    }
    ast.PTyp(u) -> #(tm.PTyp(u), v.Typ(u + 1), ctx)
    ast.PLit(lit) -> {
      let type_ = case lit {
        lit.Int(_) -> v.int_t
        lit.Float(_) -> v.float_t
      }
      #(tm.PLit(lit), type_, ctx)
    }
    ast.PLitT(lit) -> #(tm.PLitT(lit), v.Typ(0), ctx)
    ast.PAlias(pattern_ast, name) -> {
      let #(pattern, type_, ctx) = infer_pattern(ctx, pattern_ast)
      let var = #(name, Some(v.var(list.length(ctx.env))), Some(type_))
      let ctx = context.push_var(ctx, var)
      #(tm.PAlias(name, pattern), type_, ctx)
    }
    ast.PCtr(tag, pattern_ast) -> {
      let #(pattern, type_, ctx) = infer_pattern(ctx, pattern_ast)
      #(tm.PCtr(tag, pattern), v.Ctr(tag, type_), ctx)
    }
    ast.PRcd(fields_ast, tail) -> {
      let #(fields, fields_type, ctx) = infer_pattern_fields(ctx, fields_ast)
      let #(tail, tail_type, ctx) = case tail {
        None -> #(None, None, ctx)
        Some(tail) -> {
          let #(tail, tail_type, ctx) = infer_pattern(ctx, tail)
          #(Some(tail), Some(tail_type), ctx)
        }
      }
      #(tm.PRcd(fields, tail), v.Rcd(fields_type, tail_type), ctx)
    }
    ast.PErr -> #(tm.PErr, v.Err, ctx)
  }
}

fn infer_pattern_fields(
  ctx: Context,
  fields_ast: List(#(String, ast.Pattern)),
) -> #(
  List(#(String, tm.Pattern)),
  List(#(String, #(Value, Option(Value)))),
  Context,
) {
  case fields_ast {
    [] -> #([], [], ctx)
    [#(name, pattern_ast), ..fields_ast] -> {
      let #(pattern, type_, ctx) = infer_pattern(ctx, pattern_ast)
      let #(fields, fields_type, ctx) = infer_pattern_fields(ctx, fields_ast)
      #(
        [#(name, pattern), ..fields],
        [#(name, #(type_, None)), ..fields_type],
        ctx,
      )
    }
  }
}

fn check_pattern(
  ctx: Context,
  pattern_ast: ast.Pattern,
  expected: #(Value, Span),
) -> #(tm.Pattern, Context) {
  let #(pattern, inferred, ctx) = infer_pattern(ctx, pattern_ast)
  let ctx = case expected {
    // Don't constrain the expected type when it's neutral —
    // different match cases may have different pattern types
    // for function overloading.
    #(v.Neut(_), _) -> ctx
    _ -> unify(ctx, #(inferred, pattern_ast.span), expected)
  }
  #(pattern, ctx)
}

fn bind_guard(
  ctx: Context,
  guard_ast: Option(#(Expr, ast.Pattern)),
) -> #(Option(#(tm.Term, tm.Pattern)), Context) {
  case guard_ast {
    None -> #(None, ctx)
    Some(#(ast, pattern_ast)) -> {
      let #(term, type_, ctx) = infer(ctx, ast)
      let #(pattern, ctx) = check_pattern(ctx, pattern_ast, #(type_, ast.span))
      #(Some(#(term, pattern)), ctx)
    }
  }
}

fn infer_err(ctx: Context) -> #(Term, Value, Context) {
  #(tm.Err, v.Err, ctx)
}
