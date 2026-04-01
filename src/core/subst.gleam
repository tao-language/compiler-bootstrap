// ============================================================================
// CORE SUBST - Substitution and Forcing
// ============================================================================
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state

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
                Ok(solution) -> force_value(ffi, sub, solution, steps - 1)
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
    ast.VCall(_, args) -> {
      list.fold(args, acc, fn(acc_holes, a) {
        free_holes_value_loop(a, seen, acc_holes)
      })
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
