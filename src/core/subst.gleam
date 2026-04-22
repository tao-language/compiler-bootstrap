// ============================================================================
// CORE SUBST - Substitution and Forcing
// ============================================================================
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state
import core/eval as eval
import core/visitor as visitor

pub fn force(ffi: state.FFI, sub: ast.Subst, value: ast.Value) -> ast.Value {
  force_value(ffi, sub, value, 100)
}

fn force_value(ffi: state.FFI, sub: ast.Subst, value: ast.Value, steps: Int) -> ast.Value {
  case steps <= 0 {
    True -> value
    False -> {
      case value {
        ast.VNeut(head, spine) -> {
          case head {
            ast.HHole(id) -> {
              case list.key_find(sub, id) {
                Ok(solution) -> {
                  // Force the solution and apply the spine
                  let forced_solution = force_value(ffi, sub, solution, steps - 1)
                  apply_spine(ffi, sub, forced_solution, spine, steps - 1)
                }
                Error(Nil) -> value
              }
            }
            _ -> {
              let new_spine = list.map(spine, fn(e) { force_elim(ffi, sub, e) })
              ast.VNeut(head, new_spine)
            }
          }
        }
        _ -> value
      }
    }
  }
}

fn apply_spine(
  ffi: state.FFI,
  sub: ast.Subst,
  value: ast.Value,
  spine: List(ast.Elim),
  steps: Int,
) -> ast.Value {
  case spine {
    [] -> value
    [first, ..rest] -> {
      case first {
        ast.EApp(arg) -> {
          let forced_arg = force_value(ffi, sub, arg, steps - 1)
          case value {
            ast.VLam(_, _, env, body) -> {
              // Apply the lambda: substitute the argument into the body
              let new_env = [forced_arg, ..env]
              let body_value = eval.eval(ffi, new_env, body)
              apply_spine(ffi, sub, body_value, rest, steps - 1)
            }
            _ -> {
              // Can't apply, keep as neutral with spine
              ast.VNeut(ast.HStepLimit, [first, ..build_spine_from_value(value)])
            }
          }
        }
        ast.EDot(name) -> {
          case value {
            ast.VRcd(fields) -> {
              case list.key_find(fields, name) {
                Ok(field_val) -> apply_spine(ffi, sub, field_val, rest, steps - 1)
                Error(Nil) -> ast.VNeut(ast.HStepLimit, [first, ..build_spine_from_value(value)])
              }
            }
            _ -> ast.VNeut(ast.HStepLimit, [first, ..build_spine_from_value(value)])
          }
        }
        ast.EAppImplicit(_) | ast.EMatch(_, _, _) -> {
          // Can't reduce these during forcing, keep as neutral
          ast.VNeut(ast.HStepLimit, [first, ..build_spine_from_value(value)])
        }
      }
    }
  }
}

fn build_spine_from_value(value: ast.Value) -> List(ast.Elim) {
  case value {
    ast.VNeut(_, spine) -> spine
    _ -> []
  }
}

fn force_elim(ffi: state.FFI, sub: ast.Subst, elim: ast.Elim) -> ast.Elim {
  case elim {
    ast.EDot(name) -> ast.EDot(name)
    ast.EApp(arg) -> ast.EApp(force_value(ffi, sub, arg, 100))
    ast.EAppImplicit(value) -> ast.EAppImplicit(force_value(ffi, sub, value, 100))
    ast.EMatch(env, motive, cases) -> {
      let new_motive = force_value(ffi, sub, motive, 100)
      ast.EMatch(env, new_motive, cases)
    }
  }
}

pub fn ctr_solve_params(
  s: state.State,
  ctr: ast.CtrDef,
  params: List(Int),
  tag: String,
  span: Span,
) -> #(ast.Env, state.State) {
  list.fold(params, #([], s), fn(acc, id) {
    let #(acc_params, s) = acc
    case list.key_find(s.subst, id) {
      Ok(v) -> #([v, ..acc_params], s)
      Error(Nil) -> {
        let err = state.CtrUnsolvedParam(tag, ctr, id, span)
        #([ast.VErr, ..acc_params], state.State(..s, errors: list.append(s.errors, [err])))
      }
    }
  })
}

pub fn free_holes_in_value(value: ast.Value) -> List(Int) {
  free_holes_value_loop(value, [], [])
}

fn free_holes_value_loop(value: ast.Value, seen: List(Int), acc: List(Int)) -> List(Int) {
  case value {
    ast.VNeut(ast.HHole(id), spine) -> {
      case list.contains(seen, id) {
        True -> free_holes_spines(spine, seen, acc)
        False -> free_holes_spines(spine, [id, ..seen], [id, ..acc])
      }
    }
    ast.VNeut(_, spine) -> free_holes_spines(spine, seen, acc)
    ast.VLam(_, _, env, body) -> {
      let env_holes = free_holes_env(env, seen, acc)
      free_holes_term(body, seen, env_holes)
    }
    ast.VPi(_, _, env, in_val, out_term) -> {
      let in_holes = free_holes_value_loop(in_val, seen, acc)
      let env_holes = free_holes_env(env, seen, in_holes)
      free_holes_term(out_term, seen, env_holes)
    }
    ast.VRcd(fields) -> {
      list.fold(fields, acc, fn(acc_holes, f) {
        free_holes_value_loop(f.1, seen, acc_holes)
      })
    }
    ast.VRecord(fields) -> {
      list.fold(fields, acc, fn(acc_holes, f) {
        free_holes_value_loop(f.1, seen, acc_holes)
      })
    }
    ast.VCall(_, args, ret) -> {
      let acc = list.fold(args, acc, fn(acc_holes, a) {
        free_holes_value_loop(a, seen, acc_holes)
      })
      free_holes_value_loop(ret, seen, acc)
    }
    ast.VFix(_, env, body) -> {
      let env_holes = free_holes_env(env, seen, acc)
      free_holes_term(body, seen, env_holes)
    }
    ast.VCtrValue(ast.VCtr(_, arg)) -> free_holes_value_loop(arg, seen, acc)
    _ -> acc
  }
}

fn free_holes_spines(spines: List(ast.Elim), seen: List(Int), acc: List(Int)) -> List(Int) {
  list.fold(spines, acc, fn(acc_holes, e) {
    free_holes_elim(e, seen, acc_holes)
  })
}

fn free_holes_elim(elim: ast.Elim, seen: List(Int), acc: List(Int)) -> List(Int) {
  case elim {
    ast.EApp(arg) -> free_holes_value_loop(arg, seen, acc)
    ast.EAppImplicit(arg) -> free_holes_value_loop(arg, seen, acc)
    ast.EMatch(env, motive, cases) -> {
      let motive_holes = free_holes_value_loop(motive, seen, acc)
      let env_holes = free_holes_env(env, seen, motive_holes)
      free_holes_cases(cases, seen, env_holes)
    }
    _ -> acc
  }
}

fn free_holes_env(env: ast.Env, seen: List(Int), acc: List(Int)) -> List(Int) {
  list.fold(env, acc, fn(acc_holes, v) {
    free_holes_value_loop(v, seen, acc_holes)
  })
}

fn free_holes_term(term: ast.Term, seen: List(Int), acc: List(Int)) -> List(Int) {
  case term {
    ast.Hole(id, _) -> {
      case list.contains(seen, id) {
        True -> acc
        False -> [id, ..acc]
      }
    }
    ast.Lam(_, _, body, _) -> free_holes_term(body, seen, acc)
    ast.Pi(_, _, in_term, out_term, _) -> {
      let in_holes = free_holes_term(in_term, seen, acc)
      free_holes_term(out_term, seen, in_holes)
    }
    ast.App(fun, _, arg, _) -> {
      let fun_holes = free_holes_term(fun, seen, acc)
      free_holes_term(arg, seen, fun_holes)
    }
    ast.Match(arg, motive, cases, _) -> {
      let arg_holes = free_holes_term(arg, seen, acc)
      let motive_holes = free_holes_term(motive, seen, arg_holes)
      free_holes_cases(cases, seen, motive_holes)
    }
    ast.Let(_, value, body, _) -> {
      let val_holes = free_holes_term(value, seen, acc)
      free_holes_term(body, seen, val_holes)
    }
    ast.Fix(_, body, _) -> free_holes_term(body, seen, acc)
    ast.Ann(inner, _, _) -> free_holes_term(inner, seen, acc)
    ast.Rcd(fields, _) ->
      list.fold(fields, acc, fn(a, pair) { free_holes_term(pair.1, seen, a) })
    ast.Ctr(_, arg, _) -> free_holes_term(arg, seen, acc)
    ast.Dot(arg, _, _) -> free_holes_term(arg, seen, acc)
    ast.Comptime(inner, _) -> free_holes_term(inner, seen, acc)
    _ -> acc
  }
}

fn free_holes_cases(cases: List(ast.Case), seen: List(Int), acc: List(Int)) -> List(Int) {
  list.fold(cases, acc, fn(acc_holes, c) {
    let body_holes = free_holes_term(c.body, seen, acc_holes)
    case c.guard {
      Some(g) -> free_holes_term(g, seen, body_holes)
      None -> body_holes
    }
  })
}

// ============================================================================
// IMPLICIT PARAMETER INSTANTIATION
// ============================================================================

/// Instantiate implicit parameters with fresh holes.
/// Returns a substitution list mapping parameter indices to hole values.
pub fn instantiate_implicit_params(
  implicit_params: List(String),
  s: state.State,
) -> #(List(#(Int, ast.Value)), state.State) {
  instantiate_implicit_params_loop(implicit_params, s, [])
}

fn instantiate_implicit_params_loop(
  implicit_params: List(String),
  s: state.State,
  acc: List(#(Int, ast.Value)),
) -> #(List(#(Int, ast.Value)), state.State) {
  case implicit_params {
    [] -> #(list.reverse(acc), s)
    [_name, ..rest] -> {
      let #(hole_val, s) = new_hole(s)
      let index = list.length(acc)
      instantiate_implicit_params_loop(rest, s, [#(index, hole_val), ..acc])
    }
  }
}

fn new_hole(s: state.State) -> #(ast.Value, state.State) {
  let #(hole_val, s) = state.new_hole_unify(s)
  #(hole_val, s)
}

/// Substitute implicit parameter indices with their values in a value.
pub fn subst_value_with_implicit_vars(
  subst: List(#(Int, ast.Value)),
  value: ast.Value,
) -> ast.Value {
  subst_value_with_implicit_vars_loop(subst, value)
}

fn subst_value_with_implicit_vars_loop(
  subst: List(#(Int, ast.Value)),
  value: ast.Value,
) -> ast.Value {
  case value {
    ast.VNeut(ast.HVar(index), spine) -> {
      case list.key_find(subst, index) {
        Ok(replacement) -> replacement
        Error(Nil) -> ast.VNeut(ast.HVar(index), list.map(spine, fn(e) { subst_elim_with_implicit_vars(subst, e) }))
      }
    }
    ast.VRcd(fields) -> {
      ast.VRcd(list.map(fields, fn(pair) {
        #(pair.0, subst_value_with_implicit_vars_loop(subst, pair.1))
      }))
    }
    ast.VRecord(fields) -> {
      ast.VRecord(list.map(fields, fn(pair) {
        #(pair.0, subst_value_with_implicit_vars_loop(subst, pair.1))
      }))
    }
    ast.VLam(impl, name, env, body) -> {
      // Implicit param indices are not bound by lambdas, so substitute in body
      ast.VLam(impl, name, env, subst_term_with_implicit_vars(subst, body))
    }
    ast.VFix(name, env, body) -> {
      // Implicit param indices are not bound by fixpoints, so substitute in body
      ast.VFix(name, env, subst_term_with_implicit_vars(subst, body))
    }
    ast.VPi(_, _, _, domain, codomain) -> {
      // Don't substitute under Pi binders
      value
    }
    _ -> value
  }
}

/// Look up a variable index in the substitution map and convert
/// hole/var values to terms.
fn subst_lookup(subst: List(#(Int, ast.Value)), index: Int, span: Span) -> ast.Term {
  case list.key_find(subst, index) {
    Ok(ast.VNeut(ast.HHole(id), _)) -> ast.Hole(id, span)
    Ok(ast.VNeut(ast.HVar(idx), _)) -> ast.Var(idx, span)
    _ -> ast.Var(index, span)  // not in subst, keep as-is
  }
}

/// Substitute implicit parameter indices with their values in a term.
/// Uses the visitor to handle recursive traversal.
pub fn subst_term_with_implicit_vars(
  subst: List(#(Int, ast.Value)),
  term: ast.Term,
) -> ast.Term {
  visitor.visit_term(
    term,
    // var: look up in subst
    fn(idx, span) { subst_lookup(subst, idx, span) },
    // hole: not in subst (we look up var indices), keep as-is
    fn(id, span) { ast.Hole(id, span) },
    // lam: don't substitute under binders, return term unchanged
    fn(_, _, _, span) { term },
    // pi: visit both branches
    fn(implicit, name, in_t, out_t, span) { ast.Pi(implicit, name, in_t, out_t, span) },
    // app: visit fun and arg
    fn(fun, _, arg, span) { ast.App(fun, [], arg, span) },
    // match: visit arg, motive, cases
    fn(arg, motive, cases, span) {
      ast.Match(
        arg,
        motive,
        list.map(cases, fn(c) {
          ast.Case(
            pattern: visitor.visit_pattern(c.pattern,
              fn(t, p) { ast.PCtr(t, p) },
              fn(fs) { ast.PRcd(fs) },
            ),
            body: c.body,
            guard: c.guard,
            span: c.span,
          )
        }),
        span,
      )
    },
    // ctr: visit arg
    fn(tag, arg, span) { ast.Ctr(tag, arg, span) },
    // rcd: visit fields
    fn(fields, span) { ast.Rcd(fields, span) },
    // dot: visit arg
    fn(arg, name, span) { ast.Dot(arg, name, span) },
    // ann: visit inner and type
    fn(inner, ty, span) { ast.Ann(inner, ty, span) },
    // call: visit typed args and return
    fn(name, typed_args, ret, span) { ast.Call(name, typed_args, ret, span) },
    // comptime: visit inner
    fn(inner, span) { ast.Comptime(inner, span) },
    // fix: visit body
    fn(name, body, span) { ast.Fix(name, body, span) },
    // let: visit value and body
    fn(name, value, body, span) { ast.Let(name, value, body, span) },
    // typ: identity
    fn(univ, span) { ast.Typ(univ, span) },
    // lit: identity
    fn(value, span) { ast.Lit(value, span) },
    // lit_t: identity
    fn(lt, span) { ast.LitT(lt, span) },
    // unit: identity
    fn(span) { ast.Unit(span) },
    // err: identity
    fn(_, span) { ast.Err("", span) },
  )
}

fn subst_pattern_with_implicit_vars(
  subst: List(#(Int, ast.Value)),
  pattern: ast.Pattern,
) -> ast.Pattern {
  visitor.visit_pattern(pattern,
    fn(tag, p) { ast.PCtr(tag, p) },
    fn(fields) { ast.PRcd(fields) },
  )
}

fn subst_elim_with_implicit_vars(
  subst: List(#(Int, ast.Value)),
  elim: ast.Elim,
) -> ast.Elim {
  case elim {
    ast.EApp(val) -> ast.EApp(subst_value_with_implicit_vars_loop(subst, val))
    ast.EAppImplicit(val) -> ast.EAppImplicit(subst_value_with_implicit_vars_loop(subst, val))
    ast.EDot(name) -> ast.EDot(name)
    ast.EMatch(env, motive, cases) -> {
      ast.EMatch(
        env,
        motive,
        list.map(cases, fn(c) {
          ast.Case(
            pattern: c.pattern,
            body: c.body,
            guard: c.guard,
            span: c.span,
          )
        }),
      )
    }
  }
}
