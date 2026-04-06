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

// ============================================================================
// MAIN EVALUATION
// ============================================================================

pub fn eval(ffi: state.FFI, env: ast.Env, term: ast.Term) -> ast.Value {
  case term {
    ast.Typ(universe, _) -> ast.VTyp(universe)
    ast.Lit(value, _) -> ast.VLit(value)
    ast.LitT(typ, _) -> ast.VLitT(typ)
    ast.Var(index, _) -> list_get(env, index) |> result.lazy_unwrap(fn() { ast.VErr })
    ast.Hole(id, _) -> ast.VNeut(ast.HHole(id), [])
    ast.Err(_, _) -> ast.VErr
    ast.Rcd(fields, _) -> {
      let values = list.map(fields, fn(f) { #(f.0, eval(ffi, env, f.1)) })
      ast.VRcd(values)
    }
    ast.Ctr(tag, arg, _) -> ast.VCtrValue(ast.VCtr(tag, eval(ffi, env, arg)))
    ast.Unit(_) -> ast.VUnit
    ast.Dot(arg, field, span) -> do_dot(ffi, env, arg, field, span)
    ast.Ann(term, _, _) -> eval(ffi, env, term)
    ast.Lam(implicit, param, body, _) -> {
      let #(name, _) = param
      ast.VLam(implicit, name, env, body)
    }
    ast.Pi(implicit, name, in_term, out_term, _) ->
      ast.VPi(implicit, name, env, eval(ffi, env, in_term), out_term)
    ast.App(fun, implicit, arg, span) -> do_app(ffi, env, fun, implicit, arg, span)
    ast.Match(arg, motive, cases, span) -> do_match(ffi, env, arg, motive, cases, span, 100)
    ast.Call(name, args, span) -> do_call(ffi, env, name, args, span)
    ast.Comptime(term, _) -> eval(ffi, env, term)
    ast.Fix(name, body, _) -> ast.VFix(name, env, body)
    ast.Let(name, value, body, _) -> {
      let val = eval(ffi, env, value)
      eval(ffi, [val, ..env], body)
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
) -> ast.Value {
  case steps <= 0 {
    True -> ast.VErr
    False -> {
      let arg_val = eval(ffi, env, arg)
      do_match_loop(ffi, env, arg_val, motive, cases, steps)
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
) -> ast.Value {
  case cases {
    [] -> ast.VErr
    [first, ..rest] -> {
      case do_match_pattern(first.pattern, arg_val) {
        Ok(match_env) -> {
          case first.guard {
            Some(guard) -> {
              let guard_val = eval(ffi, list.append(match_env, env), guard)
              case guard_val {
                ast.VCtrValue(ast.VCtr("True", _)) -> eval(ffi, list.append(match_env, env), first.body)
                _ -> do_match_loop(ffi, env, arg_val, motive, rest, steps - 1)
              }
            }
            None -> eval(ffi, list.append(match_env, env), first.body)
          }
        }
        Error(Nil) -> do_match_loop(ffi, env, arg_val, motive, rest, steps - 1)
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

fn do_call(ffi: state.FFI, env: ast.Env, name: String, args: List(ast.Term), span: Span) -> ast.Value {
  let arg_values = list.map(args, fn(a) { eval(ffi, env, a) })
  
  case list.key_find(ffi, name) {
    Ok(state.Builtin(impl, _)) -> {
      case impl(arg_values) {
        Some(result) -> result
        None -> ast.VErr
      }
    }
    Error(Nil) -> ast.VCall(name, arg_values)
  }
}

// ============================================================================
// LIST HELPER
// ============================================================================

fn list_get(list: List(a), index: Int) -> Result(a, Nil) {
  list_get_loop(list, index, 0)
}

fn list_get_loop(list: List(a), index: Int, current: Int) -> Result(a, Nil) {
  case list {
    [] -> Error(Nil)
    [x, ..xs] -> {
      case current == index {
        True -> Ok(x)
        False -> list_get_loop(xs, index, current + 1)
      }
    }
  }
}
