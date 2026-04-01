// ============================================================================
// CORE CHECK - Type Checking
// ============================================================================
/// Bidirectional type checking: verify terms have expected types.
import gleam/list
import gleam/result
import gleam/option.{type Option, Some, None}
import syntax/grammar.{type Span, Span}
import core/ast as ast
import core/state as state
import core/eval as eval
import core/subst as subst
import core/unify as unify
import core/quote as quote

pub fn check(
  s: state.State,
  term: ast.Term,
  expected_ty: ast.Type,
  ty_span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  case term {
    ast.Fix(name, body, span) -> {
      let env = get_env(s)
      let #(_fresh, s) = def_var(s, name, expected_ty)
      let #(body_val, _, s) = check(s, body, expected_ty, span)
      let fix_val = ast.VFix(name, env, body)
      #(fix_val, expected_ty, s)
    }
    ast.Lam(implicit, param, body, span) -> {
      case expected_ty {
        ast.VPi(exp_implicit, exp_name, pi_env, domain, codomain) -> {
          let #(_fresh, s) = def_var(s, param.0, domain)
          let codomain_val = eval.eval(s.ffi, get_env(s), codomain)
          let #(body_val, _, s) = check(s, body, codomain_val, span)
          let lam_val = ast.VLam(implicit, param.0, get_env(s), body)
          #(lam_val, expected_ty, s)
        }
        _ -> {
          // For lambda without expected VPi, just return error
          let s = state.State(..s, errors: [state.TypeMismatch(ast.VErr, expected_ty, get_span(term), ty_span), ..s.errors])
          #(ast.VErr, expected_ty, s)
        }
      }
    }
    ast.Ann(inner, ann_ty, ann_span) -> {
      // Type annotation: evaluate the annotation and check inner against it
      let ann_ty_val = eval.eval(s.ffi, get_env(s), ann_ty)
      let #(_val, _ty, s) = check(s, inner, ann_ty_val, ann_span)
      let #(_new_subst, s) = unify.unify(s, 0, ann_ty_val, expected_ty, ann_span, ty_span)
      #(ast.VErr, expected_ty, s)
    }
    ast.Ctr(tag, arg, span) -> {
      case list.key_find(s.ctrs, tag) {
        Ok(ctr) -> {
          let #(params, ctr_arg_ty, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          let #(_arg_val, _, s) = check(s, arg, ctr_arg_ty, span)
          let #(_new_subst, s) = unify.unify(s, 0, ctr_ret_ty, expected_ty, span, ty_span)
          #(ast.VErr, expected_ty, s)
        }
        Error(Nil) -> {
          let s = state.State(..s, errors: [state.CtrUndefined(tag, span), ..s.errors])
          #(ast.VErr, expected_ty, s)
        }
      }
    }
    ast.Rcd(fields, span) -> {
      case expected_ty {
        ast.VRcd(expected_fields) -> {
          let #(field_vals, s) = check_fields(s, fields, expected_fields, span, ty_span)
          #(ast.VRcd(field_vals), expected_ty, s)
        }
        _ -> {
          let s = state.State(..s, errors: [state.TypeMismatch(ast.VErr, expected_ty, span, ty_span), ..s.errors])
          #(ast.VErr, expected_ty, s)
        }
      }
    }
    ast.Dot(arg, name, span) -> {
      let #(_arg_val, arg_ty, s) = check(s, arg, ast.VErr, span)
      case arg_ty {
        ast.VRcd(fields) -> {
          case list.key_find(fields, name) {
            Ok(field_ty) -> {
              let #(_new_subst, s) = unify.unify(s, 0, field_ty, expected_ty, span, ty_span)
              #(ast.VErr, expected_ty, s)
            }
            Error(Nil) -> {
              let s = state.State(..s, errors: [state.DotFieldNotFound(name, fields, span), ..s.errors])
              #(ast.VErr, expected_ty, s)
            }
          }
        }
        _ -> {
          let s = state.State(..s, errors: [state.DotOnNonCtr(arg_ty, name, span), ..s.errors])
          #(ast.VErr, expected_ty, s)
        }
      }
    }
    ast.App(fun, implicit, arg, span) -> {
      let #(fun_val, fun_ty, s) = check(s, fun, ast.VErr, span)
      case fun_ty {
        ast.VPi(_, _, env, domain, codomain) -> {
          let #(_arg_val, _, s) = check(s, arg, domain, span)
          let codomain_val = eval.eval(s.ffi, env, codomain)
          let #(_new_subst, s) = unify.unify(s, 0, codomain_val, expected_ty, span, ty_span)
          #(ast.VErr, expected_ty, s)
        }
        _ -> {
          let s = state.State(..s, errors: [state.NotAFunction(fun, fun_ty), ..s.errors])
          #(ast.VErr, expected_ty, s)
        }
      }
    }
    ast.Match(arg, motive, cases, span) -> {
      let #(_arg_val, _, s) = check(s, arg, ast.VErr, span)
      let #(_motive_val, motive_ty, s) = check(s, motive, ast.VTyp(0), span)
      let #(_new_subst, s) = unify.unify(s, 0, motive_ty, expected_ty, span, ty_span)
      #(ast.VErr, expected_ty, s)
    }
    ast.Pi(implicit, name, in_term, out_term, span) -> {
      let #(_in_val, _, s) = check(s, in_term, ast.VTyp(0), span)
      let #(_out_val, _, s) = check(s, out_term, ast.VTyp(0), span)
      let #(_new_subst, s) = unify.unify(s, 0, ast.VTyp(0), expected_ty, span, ty_span)
      #(ast.VErr, expected_ty, s)
    }
    ast.Call(name, args, span) -> {
      let #(_arg_vals, s) = check_args(s, args, span)
      let #(_new_subst, s) = unify.unify(s, 0, ast.VErr, expected_ty, span, ty_span)
      #(ast.VErr, expected_ty, s)
    }
    ast.Comptime(inner, span) -> {
      let val = eval.eval(s.ffi, [], inner)
      let quoted = quote.quote(s.ffi, 0, val, span)
      check(s, quoted, expected_ty, ty_span)
    }
    ast.Typ(k, span) -> {
      let #(_new_subst, s) = unify.unify(s, 0, ast.VTyp(k), expected_ty, span, ty_span)
      #(ast.VTyp(k), ast.VTyp(k), s)
    }
    ast.Lit(k, span) -> {
      let lit_ty = typeof_lit(k)
      let #(_new_subst, s) = unify.unify(s, 0, lit_ty, expected_ty, span, ty_span)
      #(ast.VLit(k), lit_ty, s)
    }
    ast.LitT(k, span) -> {
      let #(_new_subst, s) = unify.unify(s, 0, ast.VTyp(0), expected_ty, span, ty_span)
      #(ast.VLitT(k), ast.VTyp(0), s)
    }
    ast.Unit(span) -> {
      let #(_new_subst, s) = unify.unify(s, 0, ast.VUnit, expected_ty, span, ty_span)
      #(ast.VUnit, ast.VUnit, s)
    }
    ast.Var(i, span) -> {
      case ctx_get(s.vars, i) {
        Some(#(val, ty)) -> {
          let forced_ty = subst.force(s.ffi, s.subst, ty)
          let #(_new_subst, s) = unify.unify(s, 0, forced_ty, expected_ty, span, ty_span)
          #(val, forced_ty, s)
        }
        None -> {
          let s = state.State(..s, errors: [state.VarUndefined(i, span), ..s.errors])
          #(ast.VErr, expected_ty, s)
        }
      }
    }
    ast.Hole(id, span) -> {
      let id = s.hole_counter
      let hole_ty = ast.VNeut(ast.HHole(id), [])
      let s = state.State(..s, hole_counter: id + 1)
      let #(_new_subst, s) = unify.unify(s, 0, hole_ty, expected_ty, span, ty_span)
      #(ast.VNeut(ast.HHole(id), []), hole_ty, s)
    }
    ast.Err(_, span) -> {
      #(ast.VErr, expected_ty, s)
    }
  }
}

fn check_fields(
  s: state.State,
  fields: List(#(String, ast.Term)),
  expected_fields: List(#(String, ast.Value)),
  span: Span,
  ty_span: Span,
) -> #(List(#(String, ast.Value)), state.State) {
  check_fields_loop(s, fields, expected_fields, span, ty_span, [])
}

fn check_fields_loop(
  s: state.State,
  fields: List(#(String, ast.Term)),
  expected_fields: List(#(String, ast.Value)),
  span: Span,
  ty_span: Span,
  acc: List(#(String, ast.Value)),
) -> #(List(#(String, ast.Value)), state.State) {
  case fields {
    [] -> #(list.reverse(acc), s)
    [#(name, term), ..rest] -> {
      case list.key_find(expected_fields, name) {
        Ok(expected_ty) -> {
          let #(val, _, s) = check(s, term, expected_ty, span)
          check_fields_loop(s, rest, expected_fields, span, ty_span, [#(name, val), ..acc])
        }
        Error(Nil) -> {
          let s = state.State(..s, errors: [state.RcdMissingFields([name], span), ..s.errors])
          check_fields_loop(s, rest, expected_fields, span, ty_span, acc)
        }
      }
    }
  }
}

fn check_args(
  s: state.State,
  args: List(ast.Term),
  span: Span,
) -> #(List(ast.Value), state.State) {
  check_args_loop(s, args, span, [])
}

fn check_args_loop(
  s: state.State,
  args: List(ast.Term),
  span: Span,
  acc: List(ast.Value),
) -> #(List(ast.Value), state.State) {
  case args {
    [] -> #(list.reverse(acc), s)
    [arg, ..rest] -> {
      let #(val, _, s) = check(s, arg, ast.VErr, span)
      check_args_loop(s, rest, span, [val, ..acc])
    }
  }
}

pub fn check_type(
  s: state.State,
  t1: ast.Value,
  t2: ast.Value,
  t1_span: Span,
  t2_span: Span,
) -> #(ast.Value, state.State) {
  let #(new_subst, new_s) = unify.unify(s, 0, t1, t2, t1_span, t2_span)
  #(subst.force(new_s.ffi, new_subst, t1), new_s)
}

pub fn bind_pattern(
  s: state.State,
  pattern: ast.Pattern,
  value: ast.Value,
  expected: ast.Type,
) -> #(state.State, List(#(String, ast.Value))) {
  bind_pattern_loop(s, pattern, value, expected, [])
}

fn bind_pattern_loop(
  s: state.State,
  pattern: ast.Pattern,
  value: ast.Value,
  expected: ast.Type,
  acc: List(#(String, ast.Value)),
) -> #(state.State, List(#(String, ast.Value))) {
  case pattern {
    ast.PAs(inner_pattern, name) -> {
      let s = state.State(..s, vars: [#(name, #(value, expected)), ..s.vars])
      bind_pattern_loop(s, inner_pattern, value, expected, [#(name, value), ..acc])
    }
    ast.PCtr(tag, arg_pattern) -> {
      case value {
        ast.VCtrValue(ast.VCtr(actual_tag, arg_val)) if actual_tag == tag -> {
          bind_pattern_loop(s, arg_pattern, arg_val, expected, acc)
        }
        _ -> #(s, acc)
      }
    }
    ast.PLit(literal) -> #(s, acc)
    ast.PLitT(lit_type) -> #(s, acc)
    ast.PTyp(_) -> #(s, acc)
    ast.PRcd(_) -> #(s, acc)
    ast.PUnit -> #(s, acc)
    ast.PAny -> #(s, acc)
  }
}

pub fn check_ctr_def(
  s: state.State,
  ctr: ast.CtrDef,
) -> #(List(Int), ast.Value, ast.Value, state.State) {
  let #(params, s) =
    list.fold(ctr.params, #([], s), fn(acc, name) {
      let #(params, s) = acc
      let id = s.hole_counter
      let #(hole, s) = new_hole(s)
      let params = [id, ..params]
      let s = state.State(..s, vars: [#(name, #(hole, hole)), ..s.vars])
      #(params, s)
    })

  let arg_ty = subst_param_vars(ctr.arg_ty, params, s)
  let ret_ty = subst_param_vars(ctr.ret_ty, params, s)

  #(params, arg_ty, ret_ty, s)
}

fn subst_param_vars(term: ast.Term, params: List(Int), s: state.State) -> ast.Value {
  case term {
    ast.Var(index, _) -> {
      case get_param_hole(params, index, s) {
        Some(hole_val) -> hole_val
        None -> eval.eval(s.ffi, get_env(s), term)
      }
    }
    ast.Typ(k, _) -> ast.VTyp(k)
    ast.Lit(k, _) -> ast.VLit(k)
    ast.LitT(k, _) -> ast.VLitT(k)
    ast.Unit(_) -> ast.VUnit
    ast.Hole(id, _) -> ast.VNeut(ast.HHole(id), [])
    ast.Ann(inner, _, _) -> subst_param_vars(inner, params, s)
    ast.Lam(_, _, body, _) -> subst_param_vars(body, params, s)
    ast.Pi(_, _, in_term, out_term, _) -> {
      subst_param_vars(out_term, params, s)
    }
    ast.App(fun, _, arg, _) -> {
      subst_param_vars(fun, params, s)
    }
    ast.Rcd(fields, _) -> {
      ast.VRcd(list.map(fields, fn(pair) {
        #(pair.0, subst_param_vars(pair.1, params, s))
      }))
    }
    ast.Ctr(tag, arg, _) -> {
      ast.VCtrValue(ast.VCtr(tag, subst_param_vars(arg, params, s)))
    }
    ast.Dot(arg, name, _) -> {
      ast.VNeut(ast.HVar(0), [ast.EDot(name)])
    }
    ast.Match(_, motive, cases, _) -> {
      subst_param_vars(motive, params, s)
    }
    ast.Call(_, _, _) -> ast.VErr
    ast.Comptime(inner, _) -> subst_param_vars(inner, params, s)
    ast.Fix(_, body, _) -> subst_param_vars(body, params, s)
    ast.Err(_, _) -> ast.VErr
  }
}

fn get_param_hole(params: List(Int), index: Int, s: state.State) -> Option(ast.Value) {
  get_param_hole_loop(params, index, 0, s)
}

fn get_param_hole_loop(
  params: List(Int),
  index: Int,
  current: Int,
  s: state.State,
) -> Option(ast.Value) {
  case params {
    [] -> None
    [id, ..rest] -> {
      case current == index {
        True -> Some(ast.VNeut(ast.HHole(id), []))
        False -> get_param_hole_loop(rest, index, current + 1, s)
      }
    }
  }
}

fn get_env(s: state.State) -> ast.Env {
  list.map(s.vars, fn(pair) { pair.1.0 })
}

fn ctx_get(ctx: ast.Context, index: Int) -> Option(#(ast.Value, ast.Type)) {
  ctx_get_loop(ctx, index, 0)
}

fn ctx_get_loop(
  ctx: ast.Context,
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

fn def_var(s: state.State, name: String, ty: ast.Value) -> #(ast.Value, state.State) {
  let index = list.length(s.vars)
  let var_val = ast.VNeut(ast.HVar(index), [])
  let s = state.State(..s, vars: [#(name, #(ty, ty)), ..s.vars])
  #(var_val, s)
}

fn new_hole(s: state.State) -> #(ast.Value, state.State) {
  let id = s.hole_counter
  let hole_val = ast.VNeut(ast.HHole(id), [])
  let s = state.State(..s, hole_counter: id + 1)
  #(hole_val, s)
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
