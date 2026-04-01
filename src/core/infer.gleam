// ============================================================================
// CORE INFER - Type Inference
// ============================================================================
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/grammar.{type Span, Span}
import core/ast as ast
import core/state as state
import core/eval as eval
import core/quote as quote
import core/subst as subst
import core/check.{check, check_type, check_ctr_def}

pub fn infer(s: state.State, term: ast.Term) -> #(ast.Value, ast.Type, state.State) {
  case term {
    ast.Typ(k, span) -> #(ast.VTyp(k), ast.VTyp(k + 1), s)
    ast.Lit(k, span) -> #(ast.VLit(k), typeof_lit(k), s)
    ast.LitT(k, span) -> #(ast.VLitT(k), ast.VTyp(0), s)
    ast.Var(i, span) ->
      case ctx_get(s.vars, i) {
        Some(#(val, ty)) -> {
          let forced_ty = subst.force(s.ffi, s.subst, ty)
          #(val, forced_ty, s)
        }
        None -> {
          let s = state.State(..s, errors: [state.VarUndefined(i, span), ..s.errors])
          #(ast.VErr, ast.VErr, s)
        }
      }
    ast.Hole(id, span) -> {
      let id = s.hole_counter
      let hole_ty = ast.VNeut(ast.HHole(id), [])
      let s = state.State(..s, hole_counter: id + 1, errors: [state.HoleUnsolved(id, span), ..s.errors])
      #(ast.VNeut(ast.HHole(id), []), hole_ty, s)
    }
    ast.Rcd(fields, span) -> {
      let #(fields_val, fields_ty, s) = infer_fields(s, fields)
      #(ast.VRcd(fields_val), ast.VRcd(fields_ty), s)
    }
    ast.Ctr(tag, arg, span) ->
      case list.key_find(s.ctrs, tag) {
        Error(Nil) -> {
          let s = state.State(..s, errors: [state.CtrUndefined(tag, span), ..s.errors])
          #(ast.VErr, ast.VErr, s)
        }
        Ok(ctr) -> {
          let #(params, ctr_arg_ty, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          let #(_, arg_ty, s) = infer(s, arg)
          let #(_, s) = check_type(s, arg_ty, ctr_arg_ty, get_span(arg), get_span(ctr.arg_ty))
          let #(params, s) = subst.ctr_solve_params(s, ctr, params, tag, span)
          let env = list.append(params, get_env(s))
          let arg_val = eval.eval(s.ffi, env, arg)
          let ret_ty_val = eval.eval(s.ffi, env, ctr.ret_ty)
          #(ast.VCtrValue(ast.VCtr(tag, arg_val)), ret_ty_val, s)
        }
      }
    ast.Unit(span) -> #(ast.VUnit, ast.VTyp(0), s)
    ast.Dot(arg, name, span) -> {
      let #(arg_val, arg_ty, s) = infer(s, arg)
      case arg_ty {
        ast.VRcd(fields) ->
          case list.key_find(fields, name) {
            Ok(ty) -> {
              let val = ast.VNeut(ast.HVar(0), [ast.EDot(name)])
              #(val, ty, s)
            }
            Error(Nil) -> {
              let s = state.State(..s, errors: [state.DotFieldNotFound(name, fields, span), ..s.errors])
              #(ast.VErr, ast.VErr, s)
            }
          }
        ast.VErr -> #(ast.VErr, ast.VErr, s)
        _ -> {
          let s = state.State(..s, errors: [state.DotOnNonCtr(arg_ty, name, span), ..s.errors])
          #(ast.VErr, ast.VErr, s)
        }
      }
    }
    ast.Ann(inner, ann_ty, span) -> {
      let ty_val = eval.eval(s.ffi, get_env(s), ann_ty)
      let #(val, s) = check(s, inner, ty_val, span)
      #(val, ty_val, s)
    }
    ast.Lam(implicit, param, body, span) -> {
      let #(name, param_ty_term) = param
      let env = get_env(s)
      let holes_before = s.hole_counter

      let #(implicit_bindings, s) = create_implicit_bindings(implicit, s)
      let s = state.State(..s, vars: list.append(implicit_bindings, s.vars))

      let #(domain_val, s) = case param_ty_term {
        ast.Hole(_, _) -> new_hole(s)
        _ -> #(eval.eval(s.ffi, get_env(s), param_ty_term), s)
      }
      let #(_fresh, s) = def_var(s, name, domain_val)

      let #(body_val, body_ty, s) = infer(s, body)

      let domain_holes = subst.free_holes_in_value(domain_val)
      let codomain_holes = subst.free_holes_in_value(body_ty)
      let all_holes = list.unique(list.append(domain_holes, codomain_holes))

      let body_holes_start = holes_before + list.length(implicit)
      let holes_to_generalize =
        list.filter(all_holes, fn(id) { id >= body_holes_start })

      let has_holes = list.length(holes_to_generalize) > 0
      let #(final_implicit, final_t1, final_t2_term) = case has_holes {
        True -> {
          let quote_lvl = list.length(env) + list.length(implicit) + 1
          generalize_holes_wrapper(
            holes_to_generalize,
            implicit,
            domain_val,
            body_ty,
            s,
            s.ffi,
            quote_lvl,
            span,
          )
        }
        False -> #(
          implicit,
          domain_val,
          quote.quote(s.ffi, list.length(env) + list.length(implicit), body_ty, span),
        )
      }

      let num_new_implicit = list.length(final_implicit) - list.length(implicit)
      let quote_lvl = list.length(env) + list.length(implicit) + num_new_implicit + 1
      let body_quoted = quote.quote(s.ffi, quote_lvl, body_val, get_span(body))
      let final_t2_shifted = shift_hvar_in_term(final_t2_term, num_new_implicit)

      let vpi_env = case final_implicit {
        [] -> []
        [_] -> [ast.VNeut(ast.HVar(0), [])]
        [_, _] -> [ast.VNeut(ast.HVar(0), []), ast.VNeut(ast.HVar(1), [])]
        _ -> list.index_map(final_implicit, fn(_, idx) { ast.VNeut(ast.HVar(idx), []) })
      }
      #(
        ast.VLam(final_implicit, name, env, body_quoted),
        ast.VPi(final_implicit, name, vpi_env, final_t1, final_t2_shifted),
        s,
      )
    }
    ast.Pi(implicit, name, in_term, out_term, span) -> {
      let env = get_env(s)
      let #(in_val, _, s) = infer(s, in_term)
      let #(_, s) = def_var(s, name, in_val)
      let #(_, _, s) = infer(s, out_term)
      #(ast.VPi(implicit, name, env, in_val, out_term), ast.VTyp(0), s)
    }
    ast.App(fun, implicit, arg, span) -> infer_app(s, fun, implicit, arg, span)
    ast.Match(arg, motive, cases, span) -> infer_match(s, arg, motive, cases, span)
    ast.Call(name, args, span) -> infer_call(s, name, args, span)
    ast.Comptime(inner, span) -> {
      let val = eval.eval(s.ffi, [], inner)
      let quoted = quote.quote(s.ffi, 0, val, span)
      infer(s, quoted)
    }
    ast.Fix(name, body, span) -> infer_fix(s, name, body, span)
    ast.Err(_, span) -> #(ast.VErr, ast.VErr, s)
  }
}

fn typeof_lit(literal: ast.Literal) -> ast.Type {
  case literal {
    ast.Int(_) -> ast.VCtr("Int", ast.VUnit)
    ast.Float(_) -> ast.VCtr("Float", ast.VUnit)
    ast.Str(_) -> ast.VCtr("String", ast.VUnit)
    ast.Bool(_) -> ast.VCtr("Bool", ast.VUnit)
  }
}

fn infer_app(
  s: state.State,
  fun: ast.Term,
  implicit: List(ast.Term),
  arg: ast.Term,
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  let #(fun_val, fun_ty, s) = infer(s, fun)
  let #(arg_val, arg_ty, s) = infer(s, arg)
  
  case fun_ty {
    ast.VPi(_, _, _, domain, codomain) -> {
      let #(_, s) = check_type(s, arg_ty, domain, get_span(arg), span)
      let result_ty = subst.force(s.ffi, s.subst, codomain)
      let app_val = ast.VNeut(ast.HVar(0), [ast.EApp(arg_val)])
      #(app_val, result_ty, s)
    }
    ast.VErr -> #(ast.VErr, ast.VErr, s)
    _ -> {
      let s = state.State(..s, errors: [state.NotAFunction(fun_val, fun_ty), ..s.errors])
      #(ast.VErr, ast.VErr, s)
    }
  }
}

pub fn infer_match(
  s: state.State,
  arg: ast.Term,
  motive: ast.Term,
  cases: List(ast.Case),
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  let #(arg_val, arg_ty, s) = infer(s, arg)
  let #(motive_val, motive_ty, s) = infer(s, motive)
  
  let #(case_results, s) = infer_cases(s, cases, arg_ty, motive_val)
  
  let result_val = ast.VNeut(ast.HVar(0), [ast.EMatch([], motive_val, case_results)])
  #(result_val, motive_ty, s)
}

fn infer_cases(
  s: state.State,
  cases: List(ast.Case),
  arg_ty: ast.Type,
  motive_val: ast.Value,
) -> #(List(ast.Case), state.State) {
  infer_cases_loop(s, cases, arg_ty, motive_val, [])
}

fn infer_cases_loop(
  s: state.State,
  cases: List(ast.Case),
  arg_ty: ast.Type,
  motive_val: ast.Value,
  acc: List(ast.Case),
) -> #(List(ast.Case), state.State) {
  case cases {
    [] -> #(list.reverse(acc), s)
    [c, ..rest] -> {
      let #(patterns, body) = c
      let #(pattern_vals, s) = infer_patterns(s, patterns, arg_ty)
      let #(body_val, _, s) = infer(s, body)
      infer_cases_loop(s, rest, arg_ty, motive_val, [c, ..acc])
    }
  }
}

fn infer_patterns(
  s: state.State,
  patterns: List(ast.Pattern),
  arg_ty: ast.Type,
) -> #(List(ast.Value), state.State) {
  infer_patterns_loop(s, patterns, arg_ty, [])
}

fn infer_patterns_loop(
  s: state.State,
  patterns: List(ast.Pattern),
  arg_ty: ast.Type,
  acc: List(ast.Value),
) -> #(List(ast.Value), state.State) {
  case patterns {
    [] -> #(list.reverse(acc), s)
    [pattern, ..rest] -> {
      let #(pattern_val, s) = infer_pattern(s, pattern, arg_ty)
      infer_patterns_loop(s, rest, arg_ty, [pattern_val, ..acc])
    }
  }
}

fn infer_pattern(
  s: state.State,
  pattern: ast.Pattern,
  expected_ty: ast.Type,
) -> #(ast.Value, state.State) {
  case pattern {
    ast.PatternVar(name, span) -> {
      let hole_val = ast.VNeut(ast.HHole(0), [])
      let #(_fresh, s) = def_var(s, name, expected_ty)
      #(hole_val, s)
    }
    ast.PatternCtr(tag, arg_pattern, span) -> {
      case list.key_find(s.ctrs, tag) {
        Ok(ctr) -> {
          let #(params, ctr_arg_ty, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          let #(_, s) = check_type(s, expected_ty, ctr_ret_ty, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
          let #(arg_val, s) = infer_pattern(s, arg_pattern, ctr_arg_ty)
          #(ast.VCtrValue(ast.VCtr(tag, arg_val)), s)
        }
        Error(Nil) -> {
          let s = state.State(..s, errors: [state.CtrUndefined(tag, span), ..s.errors])
          #(ast.VErr, s)
        }
      }
    }
    ast.PatternLit(literal, span) -> {
      let val = case literal {
        ast.Int(n) -> ast.VLit(ast.Int(n))
        ast.Float(f) -> ast.VLit(ast.Float(f))
        ast.Str(str) -> ast.VLit(ast.Str(str))
        ast.Bool(b) -> ast.VLit(ast.Bool(b))
      }
      #(val, s)
    }
    ast.PatternUnit(span) -> #(ast.VUnit, s)
    ast.PatternHole(span) -> #(ast.VNeut(ast.HHole(0), []), s)
    ast.PatternErr(_, span) -> #(ast.VErr, s)
  }
}

fn infer_call(
  s: state.State,
  name: String,
  args: List(ast.Term),
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  case list.key_find(s.ffi, name) {
    Ok(state.Builtin(impl, _)) -> {
      let #(arg_vals, arg_tys, s) = infer_args(s, args)
      case impl(arg_vals) {
        Some(result_val) -> {
          let result_ty = case arg_tys {
            [ty, ..] -> ty
            [] -> ast.VErr
          }
          #(result_val, result_ty, s)
        }
        None -> {
          let result_ty = case arg_tys {
            [ty, ..] -> ty
            [] -> ast.VErr
          }
          #(ast.VCall(name, arg_vals), result_ty, s)
        }
      }
    }
    Error(Nil) -> {
      let #(arg_vals, arg_tys, s) = infer_args(s, args)
      let result_ty = case arg_tys {
        [ty, ..] -> ty
        [] -> ast.VErr
      }
      #(ast.VCall(name, arg_vals), result_ty, s)
    }
  }
}

fn infer_fix(
  s: state.State,
  name: String,
  body: ast.Term,
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  let env = get_env(s)
  case body {
    ast.Ann(lam, ann_ty, _ann_span) -> {
      let ann_ty_val = eval.eval(s.ffi, env, ann_ty)
      let #(_fresh, s) = def_var(s, name, ann_ty_val)
      let #(body_val, s) = check(s, lam, ann_ty_val, span)
      #(ast.VFix(name, env, body), ann_ty_val, s)
    }
    _ -> {
      let #(result_ty_hole, s) = new_hole(s)
      let #(_fresh, s) = def_var(s, name, result_ty_hole)
      let #(body_val, s) = check(s, body, result_ty_hole, span)
      let solved_ty = subst.force(s.ffi, s.subst, result_ty_hole)
      #(ast.VFix(name, env, body), solved_ty, s)
    }
  }
}

fn infer_args(s: state.State, args: List(ast.Term)) -> #(List(ast.Value), List(ast.Type), state.State) {
  infer_args_loop(s, args, [], [])
}

fn infer_args_loop(
  s: state.State,
  args: List(ast.Term),
  vals_acc: List(ast.Value),
  tys_acc: List(ast.Type),
) -> #(List(ast.Value), List(ast.Type), state.State) {
  case args {
    [] -> #(list.reverse(vals_acc), list.reverse(tys_acc), s)
    [arg, ..rest] -> {
      let #(val, ty, s) = infer(s, arg)
      infer_args_loop(s, rest, [val, ..vals_acc], [ty, ..tys_acc])
    }
  }
}

fn infer_fields(
  s: state.State,
  fields: List(#(String, ast.Term)),
) -> #(List(#(String, ast.Value)), List(#(String, ast.Type)), state.State) {
  infer_fields_loop(s, fields, [], [])
}

fn infer_fields_loop(
  s: state.State,
  fields: List(#(String, ast.Term)),
  vals_acc: List(#(String, ast.Value)),
  tys_acc: List(#(String, ast.Type)),
) -> #(List(#(String, ast.Value)), List(#(String, ast.Type)), state.State) {
  case fields {
    [] -> #(list.reverse(vals_acc), list.reverse(tys_acc), s)
    [#(name, term), ..rest] -> {
      let #(val, ty, s) = infer(s, term)
      infer_fields_loop(s, rest, [#(name, val), ..vals_acc], [#(name, ty), ..tys_acc])
    }
  }
}

fn ctx_get(ctx: List(#(String, #(ast.Value, ast.Type))), index: Int) -> Option(#(ast.Value, ast.Type)) {
  ctx_get_loop(ctx, index, 0)
}

fn ctx_get_loop(
  ctx: List(#(String, #(ast.Value, ast.Type))),
  index: Int,
  current: Int,
) -> Option(#(ast.Value, ast.Type)) {
  case ctx {
    [] -> None
    [#(_, val_ty), ..rest] -> {
      case current == index {
        True -> Some(val_ty)
        False -> ctx_get_loop(rest, index, current + 1)
      }
    }
  }
}

fn get_env(s: state.State) -> ast.Env {
  list.map(s.vars, fn(pair) { pair.1.0 })
}

fn def_var(s: state.State, name: String, ty: ast.Value) -> #(ast.Value, state.State) {
  let index = list.length(s.vars)
  let var_val = ast.Var(index, Span("", 0, 0, 0, 0))
  let s = state.State(..s, vars: [#(name, #(ty, ty)), ..s.vars])
  #(var_val, s)
}

fn new_hole(s: state.State) -> #(ast.Type, state.State) {
  let id = s.hole_counter
  let hole_ty = ast.VNeut(ast.HHole(id), [])
  let s = state.State(..s, hole_counter: id + 1)
  #(hole_ty, s)
}

fn create_implicit_bindings(implicit: List(ast.Term), s: state.State) -> #(List(#(String, #(ast.Value, ast.Type))), state.State) {
  create_implicit_bindings_loop(implicit, s, [])
}

fn create_implicit_bindings_loop(
  implicit: List(ast.Term),
  s: state.State,
  acc: List(#(String, #(ast.Value, ast.Type))),
) -> #(List(#(String, #(ast.Value, ast.Type))), state.State) {
  case implicit {
    [] -> #(list.reverse(acc), s)
    [ast.Hole(id, _), ..rest] -> {
      let hole_val = ast.VNeut(ast.HHole(id), [])
      let binding = #("", #(hole_val, hole_val))
      create_implicit_bindings_loop(rest, s, [binding, ..acc])
    }
    [_, ..rest] -> create_implicit_bindings_loop(rest, s, acc)
  }
}

fn generalize_holes_wrapper(
  holes: List(Int),
  implicit: List(ast.Term),
  domain: ast.Value,
  codomain: ast.Type,
  s: state.State,
  ffi: state.FFI,
  lvl: Int,
  span: Span,
) -> #(List(ast.Term), ast.Value, ast.Term) {
  // Simplified generalization - just return the inputs for now
  #(implicit, domain, quote.quote(ffi, lvl, codomain, span))
}

fn shift_hvar_in_term(term: ast.Term, shift: Int) -> ast.Term {
  case term {
    ast.Var(index, span) if index >= shift -> ast.Var(index + shift, span)
    ast.Var(_, _) -> term
    ast.Lam(implicit, param, body, span) -> {
      ast.Lam(implicit, param, shift_hvar_in_term(body, shift), span)
    }
    ast.Pi(implicit, name, in_term, out_term, span) -> {
      ast.Pi(implicit, name, shift_hvar_in_term(in_term, shift), shift_hvar_in_term(out_term, shift + 1), span)
    }
    ast.App(fun, implicit, arg, span) -> {
      ast.App(shift_hvar_in_term(fun, shift), implicit, shift_hvar_in_term(arg, shift), span)
    }
    ast.Ann(inner, ty, span) -> {
      ast.Ann(shift_hvar_in_term(inner, shift), shift_hvar_in_term(ty, shift), span)
    }
    ast.Hole(_, _) -> term
    ast.Typ(_, _) -> term
    ast.Lit(_, _) -> term
    ast.LitT(_, _) -> term
    ast.Unit(_) -> term
    ast.Rcd(fields, span) -> {
      ast.Rcd(list.map(fields, fn(pair) { #(pair.0, shift_hvar_in_term(pair.1, shift)) }), span)
    }
    ast.Ctr(tag, arg, span) -> {
      ast.Ctr(tag, shift_hvar_in_term(arg, shift), span)
    }
    ast.Dot(arg, name, span) -> {
      ast.Dot(shift_hvar_in_term(arg, shift), name, span)
    }
    ast.Match(arg, motive, cases, span) -> {
      ast.Match(
        shift_hvar_in_term(arg, shift),
        shift_hvar_in_term(motive, shift),
        list.map(cases, fn(c) {
          let #(patterns, body) = c
          #(list.map(patterns, fn(p) { shift_hvar_in_pattern(p, shift) }), shift_hvar_in_term(body, shift + list.length(patterns)))
        }),
        span,
      )
    }
    ast.Call(name, args, span) -> {
      ast.Call(name, list.map(args, fn(a) { shift_hvar_in_term(a, shift) }), span)
    }
    ast.Comptime(inner, span) -> {
      ast.Comptime(shift_hvar_in_term(inner, shift), span)
    }
    ast.Fix(name, body, span) -> {
      ast.Fix(name, shift_hvar_in_term(body, shift + 1), span)
    }
    ast.Err(_, _) -> term
  }
}

fn shift_hvar_in_pattern(pattern: ast.Pattern, shift: Int) -> ast.Pattern {
  case pattern {
    ast.PatternVar(name, span) -> ast.PatternVar(name, span)
    ast.PatternCtr(tag, arg, span) -> {
      ast.PatternCtr(tag, shift_hvar_in_pattern(arg, shift), span)
    }
    ast.PatternLit(_, _) -> pattern
    ast.PatternUnit(_) -> pattern
    ast.PatternHole(_) -> pattern
    ast.PatternErr(_, _) -> pattern
  }
}

fn get_span(term: ast.Term) -> Span {
  case term {
    ast.Typ(_, span) -> span
    ast.Lit(_, span) -> span
    ast.LitT(_, span) -> span
    ast.Var(_, span) -> span
    ast.Hole(_, span) -> span
    ast.Rcd(_, span) -> span
    ast.Ctr(_, _, span) -> span
    ast.Unit(span) -> span
    ast.Dot(_, _, span) -> span
    ast.Ann(_, _, span) -> span
    ast.Lam(_, _, _, span) -> span
    ast.Pi(_, _, _, _, span) -> span
    ast.App(_, _, _, span) -> span
    ast.Match(_, _, _, span) -> span
    ast.Call(_, _, span) -> span
    ast.Comptime(_, span) -> span
    ast.Fix(_, _, span) -> span
    ast.Err(_, span) -> span
  }
}
