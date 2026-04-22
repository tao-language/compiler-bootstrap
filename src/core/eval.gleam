// ============================================================================
// CORE EVAL
import gleam/option.{type Option, None, Some}
// ============================================================================
/// Evaluation reduces terms to values in a given environment.
import gleam/list
import gleam/result
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state
import core/list_utils as list_utils

// ============================================================================
// MAIN EVALUATION
// ============================================================================

/// Evaluate a term to a value.
///
/// Uses the language's default truth constructor ("True" for Tao).
/// For custom truth constructors, use `eval_with_ffi_config`.
pub fn eval(ffi: state.FFI, env: ast.Env, term: ast.Term) -> ast.Value {
  eval_with_ctor(ffi, env, term, "True")
}

/// Evaluate a term with a configurable truth constructor for guard evaluation.
/// The truth constructor is used in match guard evaluation to determine
/// whether a guard expression evaluates to true.
pub fn eval_with_ctor(
  ffi: state.FFI,
  env: ast.Env,
  term: ast.Term,
  truth_ctor: String,
) -> ast.Value {
  case term {
    ast.Typ(universe, _) -> ast.VTyp(universe)
    ast.Lit(value, _) -> ast.VLit(value)
    ast.LitT(typ, _) -> ast.VLitT(typ)
    ast.Var(index, _) -> list_utils.list_get(env, index) |> result.lazy_unwrap(fn() { ast.VErr })
    ast.Hole(id, _) -> ast.VNeut(ast.HHole(id), [])
    ast.Err(_, _) -> ast.VErr
    ast.Rcd(fields, _) -> {
      let values = list.map(fields, fn(f) { #(f.0, eval_with_ctor(ffi, env, f.1, truth_ctor)) })
      ast.VRcd(values)
    }
    ast.Ctr(tag, arg, _) -> ast.VCtrValue(ast.VCtr(tag, eval_with_ctor(ffi, env, arg, truth_ctor)))
    ast.Unit(_) -> ast.VUnit
    ast.Dot(arg, field, span) -> do_dot(ffi, env, arg, field, span)
    ast.Ann(term, _, _) -> eval_with_ctor(ffi, env, term, truth_ctor)
    ast.Lam(implicit, param, body, _) -> {
      let #(name, _) = param
      ast.VLam(implicit, name, env, body)
    }
    ast.Pi(implicit, name, in_term, out_term, _) ->
      ast.VPi(implicit, name, env, eval_with_ctor(ffi, env, in_term, truth_ctor), out_term)
    ast.App(fun, implicit, arg, span) -> do_app(ffi, env, fun, implicit, arg, span)
    ast.Match(arg, motive, cases, span) -> do_match(ffi, env, arg, motive, cases, span, 100, truth_ctor)
    ast.Call(name, typed_args, ret_type, span) -> do_call(ffi, env, name, typed_args, ret_type, span)
    ast.Comptime(term, _) -> eval_with_ctor(ffi, env, term, truth_ctor)
    ast.Fix(name, body, _) -> ast.VFix(name, env, body)
    ast.Let(name, value, body, _) -> {
      let val = eval_with_ctor(ffi, env, value, truth_ctor)
      eval_with_ctor(ffi, [val, ..env], body, truth_ctor)
    }
  }
}

// ============================================================================
// APPLICATION
// ============================================================================

pub fn do_app(
  ffi: state.FFI,
  env: ast.Env,
  fun: ast.Term,
  implicit: List(ast.Term),
  arg: ast.Term,
  span: Span,
) -> ast.Value {
  let fun_val = eval(ffi, env, fun)
  let arg_val = eval(ffi, env, arg)
  
  case fun_val {
    ast.VLam(_, _, closure_env, body) -> {
      eval(ffi, [arg_val, ..closure_env], body)
    }
    ast.VFix(name, fix_env, fix_body) -> {
      // Unroll the fixpoint: evaluate the fix body (should be a Lam, possibly wrapped in Ann)
      // with the argument and the fix environment extended with the VFix itself
      let body = case fix_body {
        ast.Ann(inner, _, _) -> inner
        _ -> fix_body
      }
      case body {
        ast.Lam(implicit, _param, body_term, _) -> {
          let self = ast.VFix(name, fix_env, fix_body)
          eval(ffi, [arg_val, self, ..fix_env], body_term)
        }
        _ -> ast.VErr
      }
    }
    ast.VNeut(head, spine) -> {
      ast.VNeut(head, list.append(spine, [ast.EApp(arg_val)]))
    }
    ast.VErr -> ast.VErr
    _ -> ast.VErr
  }
}

/// Evaluate with a custom truth constructor. Exposed for callers that need
/// a non-default truth constructor.
pub fn do_app_with_ctor(
  ffi: state.FFI,
  env: ast.Env,
  fun: ast.Term,
  implicit: List(ast.Term),
  arg: ast.Term,
  span: Span,
  truth_ctor: String,
) -> ast.Value {
  let fun_val = eval_with_ctor(ffi, env, fun, truth_ctor)
  let arg_val = eval_with_ctor(ffi, env, arg, truth_ctor)
  
  case fun_val {
    ast.VLam(_, _, closure_env, body) -> {
      eval_with_ctor(ffi, [arg_val, ..closure_env], body, truth_ctor)
    }
    ast.VFix(name, fix_env, fix_body) -> {
      let body = case fix_body {
        ast.Ann(inner, _, _) -> inner
        _ -> fix_body
      }
      case body {
        ast.Lam(implicit, _param, body_term, _) -> {
          let self = ast.VFix(name, fix_env, fix_body)
          eval_with_ctor(ffi, [arg_val, self, ..fix_env], body_term, truth_ctor)
        }
        _ -> ast.VErr
      }
    }
    ast.VNeut(head, spine) -> {
      ast.VNeut(head, list.append(spine, [ast.EApp(arg_val)]))
    }
    ast.VErr -> ast.VErr
    _ -> ast.VErr
  }
}

// ============================================================================
// DOT (FIELD PROJECTION)
// ============================================================================

pub fn do_dot(ffi: state.FFI, env: ast.Env, arg: ast.Term, field: String, span: Span) -> ast.Value {
  let arg_val = eval(ffi, env, arg)
  
  case arg_val {
    ast.VRcd(fields) -> {
      case list.key_find(fields, field) {
        Ok(value) -> value
        Error(Nil) -> ast.VErr
      }
    }
    ast.VNeut(head, spine) -> {
      ast.VNeut(head, list.append(spine, [ast.EDot(field)]))
    }
    _ -> ast.VErr
  }
}

// ============================================================================
// MATCH (PATTERN MATCHING)
// ============================================================================

pub fn do_match(
  ffi: state.FFI,
  env: ast.Env,
  arg: ast.Term,
  motive: ast.Term,
  cases: List(ast.Case),
  span: Span,
  steps: Int,
  truth_ctor: String,
) -> ast.Value {
  case steps <= 0 {
    True -> ast.VErr
    False -> {
      let arg_val = eval(ffi, env, arg)
      do_match_loop(ffi, env, arg_val, motive, cases, steps, truth_ctor)
    }
  }
}

fn do_match_loop(
  ffi: state.FFI,
  env: ast.Env,
  arg_val: ast.Value,
  motive: ast.Term,
  cases: List(ast.Case),
  steps: Int,
  truth_ctor: String,
) -> ast.Value {
  case cases {
    [] -> ast.VErr
    [first, ..rest] -> {
      case do_match_pattern(first.pattern, arg_val) {
        Ok(match_env) -> {
          case first.guard {
            Some(guard) -> {
              let guard_val = eval(ffi, list.append(match_env, env), guard)
              case guard_val, ast.is_true_value(guard_val, truth_ctor) {
                _, True -> eval(ffi, list.append(match_env, env), first.body)
                _, False -> do_match_loop(ffi, env, arg_val, motive, rest, steps - 1, truth_ctor)
              }
            }
            None -> eval(ffi, list.append(match_env, env), first.body)
          }
        }
        Error(Nil) -> do_match_loop(ffi, env, arg_val, motive, rest, steps - 1, truth_ctor)
      }
    }
  }
}

pub fn do_match_pattern(pattern: ast.Pattern, value: ast.Value) -> Result(ast.Env, Nil) {
  case pattern {
    ast.PAny -> Ok([value])
    ast.PAs(p, _name) -> {
      // Bind the matched value, then recurse into inner pattern
      case do_match_pattern(p, value) {
        Ok(inner_env) -> Ok([value, ..inner_env])
        Error(Nil) -> Error(Nil)
      }
    }
    ast.PTyp(_) -> Ok([value])
    ast.PLit(lit) -> {
      case value {
        ast.VLit(lit2) if lit == lit2 -> Ok([])
        _ -> Error(Nil)
      }
    }
    ast.PLitT(lit_t) -> {
      case value {
        ast.VLitT(lit_t2) if lit_t == lit_t2 -> Ok([])
        _ -> Error(Nil)
      }
    }
    ast.PRcd(fields) -> {
      case value {
        ast.VRcd(value_fields) -> {
          do_match_record_fields(fields, value_fields, [])
        }
        _ -> Error(Nil)
      }
    }
    ast.PCtr(tag, arg_pattern) -> {
      case value {
        ast.VCtrValue(ast.VCtr(tag2, arg_val)) if tag == tag2 -> {
          case do_match_pattern(arg_pattern, arg_val) {
            Ok(arg_env) -> Ok(arg_env)
            Error(e) -> Error(e)
          }
        }
        _ -> Error(Nil)
      }
    }
    ast.PUnit -> {
      case value {
        ast.VUnit -> Ok([])
        _ -> Error(Nil)
      }
    }
  }
}

fn do_match_record_fields(
  patterns: List(#(String, ast.Pattern)),
  values: List(#(String, ast.Value)),
  acc: ast.Env,
) -> Result(ast.Env, Nil) {
  case patterns {
    [] -> Ok(acc)
    [#(name, pattern), ..rest] -> {
      case list.key_find(values, name) {
        Ok(value) -> {
          case do_match_pattern(pattern, value) {
            Ok(field_env) -> do_match_record_fields(rest, values, list.append(acc, field_env))
            Error(e) -> Error(e)
          }
        }
        Error(Nil) -> Error(Nil)
      }
    }
  }
}

// ============================================================================
// CALL (FFI BUILTIN)
// ============================================================================

/// Evaluate a builtin call with typed args and return type annotation.
/// The return type is evaluated for correctness but not used in evaluation.
fn do_call(
  ffi: state.FFI,
  env: ast.Env,
  name: String,
  typed_args: List(#(ast.Term, ast.Term)),
  ret_type: ast.Term,
  span: Span,
) -> ast.Value {
  // Extract argument terms for evaluation
  let arg_terms = list.map(typed_args, fn(pair) { eval(ffi, env, pair.0) })
  // Evaluate return type annotation (for correctness, not for computation)
  let ret_val = eval_with_ctor(ffi, env, ret_type, "True")
  
  case list.key_find(ffi, name) {
    Ok(builtin) -> {
      let impl_fn = state.builtin_impl(builtin)
      case impl_fn(arg_terms) {
        Some(result) -> result
        None -> ast.VErr
      }
    }
    Error(Nil) -> ast.VCall(name: name, args: arg_terms, ret: ret_val)
  }
}

// No additional helpers needed — shared list utilities are in core/list_utils.gleam
