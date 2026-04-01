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
import core/unify as unify
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
      // Preserve negative hole IDs (special holes from desugarer)
      let hole_id = case id < 0 {
        True -> id
        False -> s.hole_counter
      }
      let hole_ty = ast.VNeut(ast.HHole(hole_id), [])
      let s = case id < 0 {
        True -> s  // Don't increment counter or add error for special holes
        False -> state.State(..s, hole_counter: s.hole_counter + 1, errors: [state.HoleUnsolved(hole_id, span), ..s.errors])
      }
      #(ast.VNeut(ast.HHole(hole_id), []), hole_ty, s)
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
      let #(val, _ty, s) = check(s, inner, ty_val, span)
      #(val, ty_val, s)
    }
    ast.Lam(implicit, param, body, span) -> {
      let #(name, param_ty_term) = param
      let env = get_env(s)
      let holes_before = s.hole_counter

      // Create implicit param placeholders (holes) for each implicit name
      let #(implicit_hole_ids, s) = create_implicit_holes(implicit, s)
      let implicit_bindings = create_implicit_bindings_from_holes(implicit, implicit_hole_ids)
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
    ast.I32(_) -> ast.VCtrValue(ast.VCtr("Int", ast.VUnit))
    ast.I64(_) -> ast.VCtrValue(ast.VCtr("Int", ast.VUnit))
    ast.U32(_) -> ast.VCtrValue(ast.VCtr("Int", ast.VUnit))
    ast.U64(_) -> ast.VCtrValue(ast.VCtr("Int", ast.VUnit))
    ast.F32(_) -> ast.VCtrValue(ast.VCtr("Float", ast.VUnit))
    ast.F64(_) -> ast.VCtrValue(ast.VCtr("Float", ast.VUnit))
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
  
  // Handle hole function types by creating a fresh VPi and unifying
  let fun_ty = case fun_ty {
    ast.VNeut(ast.HHole(id), []) -> {
      // Create a fresh VPi type for the hole
      let domain_hole = ast.VNeut(ast.HHole(s.hole_counter), [])
      let s = state.State(..s, hole_counter: s.hole_counter + 1)
      let codomain_hole_term = ast.Hole(s.hole_counter, span)
      let s = state.State(..s, hole_counter: s.hole_counter + 1)
      let vpi_ty = ast.VPi([], "f", [], domain_hole, codomain_hole_term)
      // Unify the hole with the VPi type
      let #(_subst, s) = unify.unify(s, 0, ast.VNeut(ast.HHole(id), []), vpi_ty, span, span)
      vpi_ty
    }
    _ -> fun_ty
  }
  
  case fun_ty {
    ast.VPi(_, _, env, domain, codomain) -> {
      let #(_, s) = check_type(s, arg_ty, domain, get_span(arg), span)
      let codomain_val = eval.eval(s.ffi, env, codomain)
      let result_ty = subst.force(s.ffi, s.subst, codomain_val)
      let app_val = ast.VNeut(ast.HVar(0), [ast.EApp(arg_val)])
      #(app_val, result_ty, s)
    }
    ast.VErr -> #(ast.VErr, ast.VErr, s)
    _ -> {
      let s = state.State(..s, errors: [state.NotAFunction(fun, fun_ty), ..s.errors])
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
  
  // First infer all case bodies to get their types
  let #(case_results, case_tys, s) = infer_cases_with_types(s, cases, arg_ty)
  
  // Now infer the motive and unify with case body types
  let #(motive_val, motive_ty, s) = infer(s, motive)
  
  // Unify motive type with all case body types
  let s = unify_motive_with_cases(s, motive_ty, case_tys, span)
  
  // Solve hole -999 in the motive body with the unified result type
  // This is a special hole used by the desugarer as a placeholder
  let s = solve_motive_hole(s, motive_val, motive_ty)
  
  let result_val = ast.VNeut(ast.HVar(0), [ast.EMatch([], motive_val, case_results)])
  #(result_val, motive_ty, s)
}

fn solve_motive_hole(s: state.State, motive_val: ast.Value, motive_ty: ast.Type) -> state.State {
  // Extract the body term from the motive lambda
  case motive_val {
    ast.VLam(_, _, _, body_term) -> {
      // If the body is a hole -999, solve it with the motive type (result type)
      case body_term {
        ast.Hole(hole_id, _) if hole_id == -999 -> {
          // Add substitution: hole -999 = motive_ty (as a value)
          let s = state.State(..s, subst: [ #(hole_id, motive_ty), ..s.subst ])
          s
        }
        _ -> s
      }
    }
    _ -> s
  }
}

fn infer_cases_with_types(
  s: state.State,
  cases: List(ast.Case),
  arg_ty: ast.Type,
) -> #(List(ast.Case), List(ast.Type), state.State) {
  infer_cases_with_types_loop(s, cases, arg_ty, [], [])
}

fn infer_cases_with_types_loop(
  s: state.State,
  cases: List(ast.Case),
  arg_ty: ast.Type,
  acc_cases: List(ast.Case),
  acc_tys: List(ast.Type),
) -> #(List(ast.Case), List(ast.Type), state.State) {
  case cases {
    [] -> #(list.reverse(acc_cases), list.reverse(acc_tys), s)
    [c, ..rest] -> {
      let patterns = [c.pattern]
      let body = c.body
      let #(_pattern_vals, s) = infer_patterns(s, patterns, arg_ty)
      let #(body_val, body_ty, s) = infer(s, body)
      infer_cases_with_types_loop(s, rest, arg_ty, [c, ..acc_cases], [body_ty, ..acc_tys])
    }
  }
}

fn unify_motive_with_cases(
  s: state.State,
  motive_ty: ast.Type,
  case_tys: List(ast.Type),
  span: Span,
) -> state.State {
  // Extract the codomain from the motive VPi type
  let motive_result_ty = case motive_ty {
    ast.VPi(_, _, env, _domain, codomain) -> eval.eval(s.ffi, env, codomain)
    _ -> motive_ty
  }
  unify_motive_loop(s, motive_result_ty, case_tys, span)
}

fn unify_motive_loop(
  s: state.State,
  motive_result_ty: ast.Type,
  case_tys: List(ast.Type),
  span: Span,
) -> state.State {
  case case_tys {
    [] -> s
    [case_ty, ..rest] -> {
      let #(_subst, s) = unify.unify(s, 0, motive_result_ty, case_ty, span, span)
      unify_motive_loop(s, motive_result_ty, rest, span)
    }
  }
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
      let patterns = [c.pattern]
      let body = c.body
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
    ast.PAs(inner_pattern, name) -> {
      let hole_val = ast.VNeut(ast.HHole(0), [])
      let #(_fresh, s) = def_var(s, name, expected_ty)
      infer_pattern(s, inner_pattern, expected_ty)
    }
    ast.PCtr(tag, arg_pattern) -> {
      case list.key_find(s.ctrs, tag) {
        Ok(ctr) -> {
          let #(params, ctr_arg_ty, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          let #(_, s) = check_type(s, expected_ty, ctr_ret_ty, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
          let #(arg_val, s) = infer_pattern(s, arg_pattern, ctr_arg_ty)
          #(ast.VCtrValue(ast.VCtr(tag, arg_val)), s)
        }
        Error(Nil) -> {
          let s = state.State(..s, errors: [state.CtrUndefined(tag, Span("", 0, 0, 0, 0)), ..s.errors])
          #(ast.VErr, s)
        }
      }
    }
    ast.PLit(literal) -> {
      let val = case literal {
        ast.I32(n) -> ast.VLit(ast.I32(n))
        ast.I64(n) -> ast.VLit(ast.I64(n))
        ast.U32(n) -> ast.VLit(ast.U32(n))
        ast.U64(n) -> ast.VLit(ast.U64(n))
        ast.F32(f) -> ast.VLit(ast.F32(f))
        ast.F64(f) -> ast.VLit(ast.F64(f))
      }
      #(val, s)
    }
    ast.PLitT(lit_type) -> #(ast.VLitT(lit_type), s)
    ast.PTyp(k) -> #(ast.VTyp(k), s)
    ast.PRcd(fields) -> {
      let #(field_vals, s) = infer_pattern_fields(s, fields)
      #(ast.VRcd(field_vals), s)
    }
    ast.PUnit -> #(ast.VUnit, s)
    ast.PAny -> #(ast.VNeut(ast.HHole(0), []), s)
  }
}

fn infer_pattern_fields(
  s: state.State,
  fields: List(#(String, ast.Pattern)),
) -> #(List(#(String, ast.Value)), state.State) {
  infer_pattern_fields_loop(s, fields, [])
}

fn infer_pattern_fields_loop(
  s: state.State,
  fields: List(#(String, ast.Pattern)),
  acc: List(#(String, ast.Value)),
) -> #(List(#(String, ast.Value)), state.State) {
  case fields {
    [] -> #(list.reverse(acc), s)
    [#(name, pattern), ..rest] -> {
      let #(val, s) = infer_pattern(s, pattern, ast.VErr)
      infer_pattern_fields_loop(s, rest, [#(name, val), ..acc])
    }
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
      let #(body_val, _ty, s) = check(s, lam, ann_ty_val, span)
      #(ast.VFix(name, env, body), ann_ty_val, s)
    }
    _ -> {
      let #(result_ty_hole, s) = new_hole(s)
      let #(_fresh, s) = def_var(s, name, result_ty_hole)
      let #(body_val, _ty, s) = check(s, body, result_ty_hole, span)
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
  let var_val = ast.VNeut(ast.HVar(index), [])
  let s = state.State(..s, vars: [#(name, #(ty, ty)), ..s.vars])
  #(var_val, s)
}

fn new_hole(s: state.State) -> #(ast.Type, state.State) {
  let id = s.hole_counter
  let hole_ty = ast.VNeut(ast.HHole(id), [])
  let s = state.State(..s, hole_counter: id + 1)
  #(hole_ty, s)
}

fn create_implicit_holes(implicit: List(String), s: state.State) -> #(List(Int), state.State) {
  create_implicit_holes_loop(implicit, s, [])
}

fn create_implicit_holes_loop(
  implicit: List(String),
  s: state.State,
  acc: List(Int),
) -> #(List(Int), state.State) {
  case implicit {
    [] -> #(list.reverse(acc), s)
    [_name, ..rest] -> {
      let id = s.hole_counter
      let s = state.State(..s, hole_counter: id + 1)
      create_implicit_holes_loop(rest, s, [id, ..acc])
    }
  }
}

fn create_implicit_bindings_from_holes(implicit: List(String), hole_ids: List(Int)) -> List(#(String, #(ast.Value, ast.Type))) {
  create_implicit_bindings_loop(implicit, hole_ids, [])
}

fn create_implicit_bindings_loop(
  implicit: List(String),
  hole_ids: List(Int),
  acc: List(#(String, #(ast.Value, ast.Type))),
) -> List(#(String, #(ast.Value, ast.Type))) {
  case implicit, hole_ids {
    [], _ -> list.reverse(acc)
    _, [] -> list.reverse(acc)
    [name, ..names], [id, ..ids] -> {
      let hole_val = ast.VNeut(ast.HHole(id), [])
      let binding = #(name, #(hole_val, hole_val))
      create_implicit_bindings_loop(names, ids, [binding, ..acc])
    }
  }
}

fn generalize_holes_wrapper(
  holes: List(Int),
  implicit: List(String),
  domain: ast.Value,
  codomain: ast.Type,
  s: state.State,
  ffi: state.FFI,
  lvl: Int,
  span: Span,
) -> #(List(String), ast.Value, ast.Term) {
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
          let shifted_pattern = shift_hvar_in_pattern(c.pattern, shift)
          let shifted_body = shift_hvar_in_term(c.body, shift + 1)
          ast.Case(pattern: shifted_pattern, body: shifted_body, guard: c.guard, span: c.span)
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
    ast.PAs(inner, name) -> ast.PAs(shift_hvar_in_pattern(inner, shift), name)
    ast.PCtr(tag, arg) -> ast.PCtr(tag, shift_hvar_in_pattern(arg, shift))
    ast.PLit(_) -> pattern
    ast.PLitT(_) -> pattern
    ast.PTyp(_) -> pattern
    ast.PRcd(fields) -> ast.PRcd(list.map(fields, fn(pair) {
      #(pair.0, shift_hvar_in_pattern(pair.1, shift))
    }))
    ast.PUnit -> pattern
    ast.PAny -> pattern
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
