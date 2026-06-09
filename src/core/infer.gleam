/// Type Inference — Bidirectional Type Checking
///
/// The `infer` module implements bidirectional type checking for the Core
/// language. Every term can be synthesized (inferred), and `check` is a
/// thin wrapper that synthesizes the term then unifies its type with
/// the expected type.
import core/ast.{type AST}
import core/coerce.{coerce}
import core/context.{type Context}
import core/eval.{eval}
import core/literals.{type Literal, type LiteralType} as lit
import core/quote.{quote}
import core/term.{type Pattern, type Term} as tm
import core/unify.{unify}
import core/unwrap.{unwrap, unwrap_term}
import core/value.{type Value} as v
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}

/// Infer the type of a term (synthesis).
///
/// Returns #(result_term, type_value, ctx) where:
/// - result_term is the original term with holes filled and implicit args expanded
/// - type_value is the inferred type (a Value)
/// - ctx is the updated ctx with any new bindings
pub fn infer(ctx: Context, ast: AST) -> #(Term, Value, Context) {
  case ast.data {
    ast.Typ(level) -> infer_typ(ctx, level)
    ast.Hole(id) -> infer_hole(ctx, id)
    ast.Lit(value) -> infer_lit(ctx, value)
    ast.LitT(t) -> infer_litt(ctx, t)
    ast.Var(name) -> infer_var(ctx, name, ast.span)
    ast.Ctr(tag, arg) -> infer_ctr(ctx, tag, arg)
    ast.Rcd(fields) -> infer_rcd(ctx, fields)
    ast.RcdT(fields) -> infer_rcd_type(ctx, fields)
    ast.Call(name, args, return_type) ->
      infer_call(ctx, name, args, return_type)
    ast.Ann(inner, type_) -> infer_ann(ctx, inner, type_)
    ast.Lam(implicit, param, body) -> infer_lam(ctx, implicit, param, body)
    // ast.Pi(implicit, domain, codomain) ->
    //   infer_pi(ctx, implicit, domain, codomain, ast.span)
    ast.Fix(name, body) -> infer_fix(ctx, name, body, ast.span)
    ast.App(implicit, fun, arg) -> infer_app(ctx, implicit, fun, arg, ast.span)
    // ast.TypeDef(params, constructors) ->
    //   infer_type_def(ctx, params, constructors, span)
    ast.Match(arg, cases) -> infer_match(ctx, arg, cases, ast.span)
    ast.Err -> infer_err(ctx)
    _ -> todo
  }
}

/// Check that a term has the expected type (verification).
///
/// This is a thin wrapper: infer the term, then fill in any missing
/// record defaults at the value level before unifying.
pub fn check(
  ctx: Context,
  ast: AST,
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
      #(term, expected_type, ctx)
    }
  }
}

fn check_on_ast(
  ctx: Context,
  ast: AST,
  type_: AST,
) -> #(Term, #(Term, Value), Context) {
  let #(type_term, _, ctx) = infer(ctx, type_)
  let type_val = eval(ctx.ffi, ctx.env, type_term)
  let #(term, type_val, ctx) = check(ctx, ast, #(type_val, type_.span))
  #(term, #(type_term, type_val), ctx)
}

fn infer_typ(ctx: Context, level: Int) -> #(Term, Value, Context) {
  #(tm.Typ(level), v.Typ(level + 1), ctx)
}

fn infer_hole(ctx: Context, hole_id: Int) -> #(Term, Value, Context) {
  case hole_id >= 0 {
    True -> {
      // Concrete hole, create a new hole for its type.
      let #(type_id, ctx) = context.new_hole(ctx)
      #(tm.Hole(hole_id), v.hole(type_id), ctx)
    }
    False -> {
      // Unknown hole, instantiate a fresh new hole.
      let #(id, ctx) = context.new_hole(ctx)
      infer_hole(ctx, id)
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
      let ctx = context.with_err(ctx, context.VarUndefined(name, span))
      #(tm.Err, v.Err, ctx)
    }
  }
}

fn infer_ctr(ctx: Context, tag: String, arg: AST) -> #(Term, Value, Context) {
  let #(arg, arg_type, ctx) = infer(ctx, arg)
  #(tm.Ctr(tag, arg), v.Ctr(tag, arg_type), ctx)
}

fn infer_rcd(
  ctx: Context,
  fields: List(#(String, AST)),
) -> #(Term, Value, Context) {
  let #(fields, field_types, ctx) = infer_rcd_fields(ctx, fields)
  #(tm.Rcd(fields), v.RcdT(field_types), ctx)
}

fn infer_rcd_fields(
  ctx: Context,
  fields: List(#(String, AST)),
) -> #(List(#(String, Term)), List(#(String, #(Value, Option(Value)))), Context) {
  case fields {
    [] -> #([], [], ctx)
    [#(name, term), ..fields] -> {
      let #(term, type_, ctx) = infer(ctx, term)
      let #(fields, field_types, ctx) = infer_rcd_fields(ctx, fields)
      #(
        [#(name, term), ..fields],
        [#(name, #(type_, None)), ..field_types],
        ctx,
      )
    }
  }
}

fn infer_rcd_type(
  ctx: Context,
  fields: List(#(String, #(AST, option.Option(AST)))),
) -> #(Term, Value, Context) {
  let #(fields, ctx) = infer_rcd_type_fields(ctx, fields)
  #(tm.RcdT(fields), v.Typ(0), ctx)
}

fn infer_rcd_type_fields(
  ctx: Context,
  fields: List(#(String, #(AST, option.Option(AST)))),
) -> #(List(#(String, #(Term, option.Option(Term)))), Context) {
  case fields {
    [] -> #([], ctx)
    [#(name, #(type_, default)), ..fields] -> {
      let #(field, ctx) = case default {
        Some(default) -> {
          let #(default, #(type_, _), ctx) = check_on_ast(ctx, default, type_)
          let field = #(name, #(type_, Some(default)))
          #(field, ctx)
        }
        None -> {
          let #(type_, _, ctx) = infer(ctx, type_)
          let field = #(name, #(type_, None))
          #(field, ctx)
        }
      }
      let #(fields, ctx) = infer_rcd_type_fields(ctx, fields)
      #([field, ..fields], ctx)
    }
  }
}

fn infer_call(
  ctx: Context,
  name: String,
  args: List(AST),
  return_type: AST,
) -> #(Term, Value, Context) {
  let #(args, ctx) = check_call_args(ctx, args)
  let #(return_type, _, ctx) = infer(ctx, return_type)
  let return_type_val = eval(ctx.ffi, ctx.env, return_type)
  #(tm.Call(name, args), return_type_val, ctx)
}

fn check_call_args(ctx: Context, args: List(AST)) -> #(List(Term), Context) {
  case args {
    [] -> #([], ctx)
    [arg, ..args] -> {
      let #(arg, _, ctx) = infer(ctx, arg)
      let #(args, ctx) = check_call_args(ctx, args)
      #([arg, ..args], ctx)
    }
  }
}

fn infer_ann(ctx: Context, ast: AST, type_: AST) -> #(Term, Value, Context) {
  let #(term, #(_, type_val), ctx) = check_on_ast(ctx, ast, type_)
  #(term, type_val, ctx)
}

fn infer_lam(
  ctx: Context,
  implicit: Bool,
  named_param: #(String, AST),
  body: AST,
) -> #(Term, Value, Context) {
  let #(name, param_ast) = named_param
  let #(param, _, ctx) = infer(ctx, param_ast)
  let param_val = eval(ctx.ffi, ctx.env, param)
  let level = list.length(ctx.env)
  let ctx = context.push_var(ctx, #(name, Some(v.var(level)), Some(param_val)))
  let #(body, body_type_val, ctx) = infer(ctx, body)
  let body_type = quote(ctx.ffi, level + 1, body_type_val)
  let ctx = context.pop_vars(ctx, 1)
  #(
    tm.Lam(#(name, param), body),
    v.Pi(ctx.env, implicit, #(name, param_val), body_type),
    ctx,
  )
}

/// Infer a Pi type: $pi<implicits>(domain: param_type) -> codomain
fn infer_pi(
  ctx: Context,
  implicit: Bool,
  domain: #(String, AST),
  codomain: AST,
  span: Span,
) -> #(Term, Value, Context) {
  // let #(implicits, _, ctx) = push_param_list(ctx, implicits)
  // let #(domain, _, ctx) = push_param(ctx, domain)
  // let #(codomain, _, ctx) = infer(ctx, codomain)
  // let ctx = pop_params(ctx, list.length(implicits) + 1)
  // #(ast.Pi(implicits, domain, codomain, span), ast.VTyp(0), ctx)
  todo
}

fn infer_fix(
  ctx: Context,
  name: String,
  body: AST,
  span: Span,
) -> #(Term, Value, Context) {
  let level = list.length(ctx.env)
  let #(hole_id, ctx) = context.new_hole(ctx)
  let type_hole = v.hole(hole_id)
  let ctx = context.push_var(ctx, #(name, Some(v.var(level)), Some(type_hole)))
  let #(body, body_type, ctx) = infer(ctx, body)
  let ctx = context.pop_vars(ctx, 1)
  let ctx = unify(ctx, #(type_hole, span), #(body_type, span))
  #(tm.Fix(name, body), body_type, ctx)
}

fn infer_app(
  ctx: Context,
  app_implicit: Bool,
  fun_ast: AST,
  arg_ast: AST,
  span: Span,
) -> #(Term, Value, Context) {
  let #(fun, fun_type, ctx) = infer(ctx, fun_ast)
  let fun_data = #(fun, fun_type, fun_ast.span)
  infer_app_args(ctx, app_implicit, fun_data, arg_ast, span)
}

fn infer_app_args(
  ctx: Context,
  app_implicit: Bool,
  fun_typed: #(Term, Value, Span),
  arg_ast: AST,
  span: Span,
) -> #(Term, Value, Context) {
  let #(fun, fun_type, fun_span) = fun_typed
  case unwrap(ctx.ffi, ctx.subst, fun_type) {
    v.Pi(pi_env, pi_implicit, #(_, domain_val), codomain) ->
      case pi_implicit, app_implicit {
        // pi_implicit, app_implicit | pi_explicit, app_explicit
        True, True | False, False -> {
          // Matching implicit/explicit argument application
          let #(arg, _, ctx) = check(ctx, arg_ast, #(domain_val, fun_span))
          let pi_env = [eval(ctx.ffi, ctx.env, arg), ..pi_env]
          let type_ = eval(ctx.ffi, pi_env, codomain)
          #(tm.App(fun, arg), unwrap(ctx.ffi, ctx.subst, type_), ctx)
        }
        // pi_implicit, app_explicit
        True, False as app_explicit -> {
          // Implicit argument expansion
          let #(hole_id, ctx) = context.new_hole(ctx)
          let fun = tm.App(fun, tm.Hole(hole_id))
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
          let error = context.AppExpectedExplicitArg(fun_type, span)
          #(tm.Err, v.Err, context.with_err(ctx, error))
        }
      }
    // Not a function type
    _ -> {
      // Still infer the arg to get as much additional information as possible in
      // the context, it might be solving holes for other parts of the program.
      let #(_, _, ctx) = infer(ctx, arg_ast)
      let error = context.NotAFunction(fun, fun_type, fun_span)
      #(tm.Err, v.Err, context.with_err(ctx, error))
    }
  }
}

fn infer_match(
  ctx: Context,
  arg_ast: AST,
  cases_ast: List(ast.Case),
  span: Span,
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
  case pattern_ast {
    ast.PAny(_) -> {
      let #(id, ctx) = context.new_hole(ctx)
      #(tm.PAny, v.hole(id), ctx)
    }
    ast.PTyp(u, _) -> #(tm.PTyp(u), v.Typ(u + 1), ctx)
    ast.PLit(lit, _) -> {
      let type_ = case lit {
        lit.Int(_) -> v.int_t
        lit.Float(_) -> v.float_t
      }
      #(tm.PLit(lit), type_, ctx)
    }
    ast.PLitT(lit, _) -> #(tm.PLitT(lit), v.Typ(0), ctx)
    ast.PAlias(name, pattern_ast, _) -> {
      let #(pattern, type_, ctx) = infer_pattern(ctx, pattern_ast)
      let var = #(name, Some(v.var(list.length(ctx.env))), Some(type_))
      let ctx = context.push_var(ctx, var)
      #(tm.PAlias(name, pattern), type_, ctx)
    }
    ast.PCtr(tag, pattern_ast, _) -> {
      let #(pattern, type_, ctx) = infer_pattern(ctx, pattern_ast)
      #(tm.PCtr(tag, pattern), v.Ctr(tag, type_), ctx)
    }
    ast.PRcd(fields, _) -> todo
    ast.PErr(_) -> #(tm.PErr, v.Err, ctx)
  }
}

fn check_pattern(
  ctx: Context,
  pattern_ast: ast.Pattern,
  expected: #(Value, Span),
) -> #(tm.Pattern, Context) {
  let #(pattern, inferred, ctx) = infer_pattern(ctx, pattern_ast)
  let ctx = unify(ctx, #(inferred, ast.pattern_span(pattern_ast)), expected)
  #(pattern, ctx)
}

fn bind_guard(
  ctx: Context,
  guard_ast: Option(#(AST, ast.Pattern)),
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
