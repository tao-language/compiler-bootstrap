// ============================================================================
// CORE UNIFY - Unification Algorithm
// ============================================================================
/// Unification checks type equality and solves metavariables (holes).
///
/// Returns Ok(state) with updated substitution if unification succeeds.
/// Returns Error if values are incompatible (type error).
import gleam/list
import gleam/result
import gleam/option.{Some, None}
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state
import core/eval as eval
import core/subst as subst

pub fn unify(
  s: state.State,
  lvl: Int,
  v1: ast.Value,
  v2: ast.Value,
  s1: Span,
  s2: Span,
) -> #(ast.Subst, state.State) {
  case unify_result(s, v1, v2, s1, s2) {
    Ok(new_s) -> #(new_s.subst, new_s)
    Error(err) -> {
      let new_s = state.State(..s, errors: [err, ..s.errors])
      #(new_s.subst, new_s)
    }
  }
}

pub fn unify_result(
  s: state.State,
  v1: ast.Value,
  v2: ast.Value,
  s1: Span,
  s2: Span,
) -> Result(state.State, state.Error) {
  case v1, v2 {
    ast.VTyp(k1), ast.VTyp(k2) if k1 == k2 -> Ok(s)
    ast.VLit(k1), ast.VLit(k2) if k1 == k2 -> Ok(s)
    ast.VLitT(k1), ast.VLitT(k2) if k1 == k2 -> Ok(s)
    // Overloaded literal types resolve to compatible concrete types
    ast.VLitT(_), ast.VLitT(_) ->
      case lit_types_unify(v1, v2) {
        True -> Ok(s)
        False -> Error(state.TypeMismatch(v2, v1, s2, s1))
      }
    ast.VNeut(ast.HHole(id), []), _ ->
      case list.key_find(s.subst, id) {
        Ok(v) -> unify_result(s, v, v2, s1, s2)
        Error(Nil) -> {
          case v2 {
            ast.VNeut(ast.HHole(id2), []) if id == id2 -> Ok(s)
            ast.VNeut(ast.HStepLimit, _) -> Ok(s)
            _ -> {
              case occurs(s.subst, id, v2) {
                True -> Error(state.InfiniteType(id, v2, s1, s2))
                False -> Ok(state.State(..s, subst: [#(id, v2), ..s.subst]))
              }
            }
          }
        }
      }
    _, ast.VNeut(ast.HHole(_), []) -> unify_result(s, v2, v1, s2, s1)
    ast.VNeut(ast.HStepLimit, _), ast.VNeut(ast.HStepLimit, _) -> Ok(s)
    ast.VNeut(h1, spine1), ast.VNeut(h2, spine2) if h1 == h2 ->
      unify_elim_list(s, spine1, spine2, s1, s2)
    ast.VRcd(fields1), ast.VRcd(fields2) -> unify_fields(s, fields1, fields2, s1, s2)
    ast.VCtrValue(ast.VCtr(k1, arg1)), ast.VCtrValue(ast.VCtr(k2, arg2)) if k1 == k2 ->
      unify_result(s, arg1, arg2, s1, s2)
    ast.VUnit, ast.VUnit -> Ok(s)
    ast.VLam(_, _, env1, body1), ast.VLam(_, _, env2, body2) -> {
      let #(fresh, s) = new_var(s)
      let a = eval.eval(s.ffi, [fresh, ..env1], body1)
      let b = eval.eval(s.ffi, [fresh, ..env2], body2)
      unify_result(s, a, b, s1, s2)
    }
    ast.VPi(_, _, env1, in1, out1), ast.VPi(_, _, env2, in2, out2) -> {
      // Unify domains first
      use s <- result.try(unify_result(s, in1, in2, s1, s2))
      // Then unify codomains by applying both to a fresh variable
      let #(fresh, s) = new_var(s)
      let a = eval.eval(s.ffi, [fresh, ..env1], out1)
      let b = eval.eval(s.ffi, [fresh, ..env2], out2)
      unify_result(s, a, b, s1, s2)
    }
    ast.VErr, _ -> Ok(s)
    _, ast.VErr -> Ok(s)
    _, _ -> Error(state.TypeMismatch(v2, v1, s2, s1))
  }
}

fn unify_fields(
  s: state.State,
  fields1: List(#(String, ast.Value)),
  fields2: List(#(String, ast.Value)),
  s1: Span,
  s2: Span,
) -> Result(state.State, state.Error) {
  case fields1 {
    [] ->
      case list.map(fields2, fn(kv) { kv.0 }) {
        [] -> Ok(s)
        names -> Error(state.RcdMissingFields(names, s1))
      }
    [#(name, v1), ..rest1] ->
      case list.key_pop(fields2, name) {
        Error(Nil) -> {
          let names =
            list.filter(rest1, fn(kv) {
              list.key_find(fields2, kv.0) == Error(Nil)
            })
            |> list.map(fn(kv) { kv.0 })
          Error(state.RcdMissingFields([name, ..names], s2))
        }
        Ok(#(v2, rest2)) -> {
          use s <- result.try(unify_result(s, v1, v2, s1, s2))
          unify_fields(s, rest1, rest2, s1, s2)
        }
      }
  }
}

fn unify_elim(
  s: state.State,
  e1: ast.Elim,
  e2: ast.Elim,
  s1: Span,
  s2: Span,
) -> Result(state.State, state.Error) {
  case e1, e2 {
    ast.EDot(n1), ast.EDot(n2) if n1 == n2 -> Ok(s)
    ast.EApp(a1), ast.EApp(a2) -> unify_result(s, a1, a2, s1, s2)
    _, _ -> Error(state.SpineMismatch(s1, s2))
  }
}

fn unify_elim_list(
  s: state.State,
  l1: List(ast.Elim),
  l2: List(ast.Elim),
  s1: Span,
  s2: Span,
) -> Result(state.State, state.Error) {
  case l1, l2 {
    [], [] -> Ok(s)
    [e1, ..xs], [e2, ..ys] -> {
      use s <- result.try(unify_elim(s, e1, e2, s1, s2))
      unify_elim_list(s, xs, ys, s1, s2)
    }
    [], _ | _, [] -> Error(state.ArityMismatch(s1, s2))
  }
}

pub fn occurs(sub: ast.Subst, id: Int, value: ast.Value) -> Bool {
  case subst.force([], sub, value) {
    ast.VTyp(_) | ast.VLit(_) | ast.VLitT(_) | ast.VErr -> False
    ast.VNeut(ast.HHole(hole_id), spine) ->
      id == hole_id || list.any(spine, occurs_elim(sub, id, _))
    ast.VNeut(ast.HStepLimit, spine) -> list.any(spine, occurs_elim(sub, id, _))
    ast.VNeut(_, spine) -> list.any(spine, occurs_elim(sub, id, _))
    ast.VRcd(fields) -> list.any(fields, fn(kv) { occurs(sub, id, kv.1) })
    ast.VCtrValue(ast.VCtr(_, arg)) -> occurs(sub, id, arg)
    ast.VUnit -> False
    // KEY FIX: Do NOT traverse environments for VLam, VPi, VFix.
    // The environment captures the typing context, but hole IDs in the
    // context values don't mean the hole appears in the TYPE.
    // Only check explicit type components (domain for VPi).
    ast.VLam(_, _, _, _) -> False
    ast.VPi(_, _, _, in_val, out_term) ->
      occurs(sub, id, in_val) || occurs_in_term(id, out_term)
    ast.VCall(_, args, ret) -> list.any(args, occurs(sub, id, _)) || occurs(sub, id, ret)
    ast.VFix(_, _, _) -> False
    ast.VRecord(fields) -> list.any(fields, fn(kv) { occurs(sub, id, kv.1) })
  }
}

/// Check if a hole ID appears in a term.
fn occurs_in_term(id: Int, term: ast.Term) -> Bool {
  case term {
    ast.Hole(hole_id, _) -> hole_id == id
    ast.Typ(_, _) -> False
    ast.Lit(_, _) -> False
    ast.LitT(_, _) -> False
    ast.Var(_, _) -> False
    ast.Err(_, _) -> False
    ast.Rcd(fields, _) -> list.any(fields, fn(kv) { occurs_in_term(id, kv.1) })
    ast.Ctr(_, arg, _) -> occurs_in_term(id, arg)
    ast.Unit(_) -> False
    ast.Dot(arg, _, _) -> occurs_in_term(id, arg)
    ast.Ann(inner, typ, _) -> occurs_in_term(id, inner) || occurs_in_term(id, typ)
    ast.Lam(_, _, body, _) -> occurs_in_term(id, body)
    ast.Pi(_, _, domain, codomain, _) ->
      occurs_in_term(id, domain) || occurs_in_term(id, codomain)
    ast.App(fun, _, arg, _) ->
      occurs_in_term(id, fun) || occurs_in_term(id, arg)
    ast.Match(arg, motive, cases, _) ->
      occurs_in_term(id, arg) || occurs_in_term(id, motive) ||
      list.any(cases, fn(c) {
        occurs_in_pattern(id, c.pattern) || occurs_in_term(id, c.body) ||
        case c.guard {
          Some(g) -> occurs_in_term(id, g)
          None -> False
        }
      })
    ast.Call(_, typed_args, ret, _) -> {
      list.any(typed_args, fn(pair) {
        occurs_in_term(id, pair.0) || occurs_in_term(id, pair.1)
      })
      || occurs_in_term(id, ret)
    }
    ast.Comptime(inner, _) -> occurs_in_term(id, inner)
    ast.Fix(_, body, _) -> occurs_in_term(id, body)
    ast.Let(_, value, body, _) -> occurs_in_term(id, value) || occurs_in_term(id, body)
  }
}

/// Check if a hole ID appears in a pattern.
fn occurs_in_pattern(id: Int, pattern: ast.Pattern) -> Bool {
  case pattern {
    ast.PAny -> False
    ast.PAs(inner, _) -> occurs_in_pattern(id, inner)
    ast.PTyp(_) -> False
    ast.PLit(_) -> False
    ast.PLitT(_) -> False
    ast.PRcd(fields) -> list.any(fields, fn(kv) { occurs_in_pattern(id, kv.1) })
    ast.PCtr(_, arg) -> occurs_in_pattern(id, arg)
    ast.PUnit -> False
  }
}

fn occurs_elim(sub: ast.Subst, id: Int, elim: ast.Elim) -> Bool {
  case elim {
    ast.EDot(_) -> False
    ast.EApp(arg) -> occurs(sub, id, arg)
    ast.EAppImplicit(arg) -> occurs(sub, id, arg)
    ast.EMatch(env, motive, _) ->
      occurs(sub, id, motive) || list.any(env, occurs(sub, id, _))
  }
}

fn new_var(s: state.State) -> #(ast.Value, state.State) {
  let var = ast.VNeut(ast.HVar(s.var_counter), [])
  #(var, state.State(..s, var_counter: s.var_counter + 1))
}

fn instantiate_implicit_params(
  implicit_params: List(ast.Term),
  s: state.State,
) -> #(List(#(Int, Int)), state.State) {
  instantiate_implicit_params_loop(implicit_params, 0, [], s)
}

fn instantiate_implicit_params_loop(
  params: List(ast.Term),
  index: Int,
  acc: List(#(Int, Int)),
  s: state.State,
) -> #(List(#(Int, Int)), state.State) {
  case params {
    [] -> #(list.reverse(acc), s)
    [_, ..rest] -> {
      let #(hole_val, s) = new_hole(s)
      let hole_id = case hole_val {
        ast.VNeut(ast.HHole(id), []) -> id
        _ -> 0
      }
      instantiate_implicit_params_loop(
        rest,
        index + 1,
        [#(index, hole_id), ..acc],
        s,
      )
    }
  }
}

fn new_hole(s: state.State) -> #(ast.Value, state.State) {
  let #(hole_val, s) = state.new_hole_unify(s)
  #(hole_val, s)
}

fn subst_value_with_implicit_vars(
  subst: List(#(Int, Int)),
  value: ast.Value,
) -> ast.Value {
  case value {
    ast.VNeut(ast.HVar(index), []) -> {
      case list.key_find(subst, index) {
        Ok(hole_id) -> ast.VNeut(ast.HHole(hole_id), [])
        Error(Nil) -> value
      }
    }
    ast.VNeut(ast.HVar(index), spine) -> {
      case list.key_find(subst, index) {
        Ok(hole_id) ->
          ast.VNeut(
            ast.HHole(hole_id),
            list.map(spine, fn(e) { subst_elim_with_implicit_vars(subst, e) }),
          )
        Error(Nil) -> value
      }
    }
    ast.VLam(implicit, name, env, body) -> {
      ast.VLam(implicit, name, env, body)
    }
    ast.VPi(implicit, name, env, in_val, out_term) -> {
      ast.VPi(implicit, name, env, in_val, out_term)
    }
    ast.VRcd(fields) -> {
      ast.VRcd(list.map(fields, fn(kv) {
        #(kv.0, subst_value_with_implicit_vars(subst, kv.1))
      }))
    }
    ast.VCtrValue(ast.VCtr(tag, arg)) -> {
      ast.VCtrValue(ast.VCtr(tag, subst_value_with_implicit_vars(subst, arg)))
    }
    ast.VCall(name, args, ret) -> {
      let shifted_args = list.map(args, fn(a) { subst_value_with_implicit_vars(subst, a) })
      ast.VCall(name, shifted_args, subst_value_with_implicit_vars(subst, ret))
    }
    ast.VFix(name, env, body) -> {
      ast.VFix(name, env, body)
    }
    _ -> value
  }
}

fn subst_elim_with_implicit_vars(
  subst: List(#(Int, Int)),
  elim: ast.Elim,
) -> ast.Elim {
  case elim {
    ast.EDot(name) -> ast.EDot(name)
    ast.EApp(arg) -> ast.EApp(subst_value_with_implicit_vars(subst, arg))
    ast.EAppImplicit(arg) -> ast.EAppImplicit(subst_value_with_implicit_vars(subst, arg))
    ast.EMatch(env, motive, cases) -> {
      ast.EMatch(
        list.map(env, fn(v) { subst_value_with_implicit_vars(subst, v) }),
        subst_value_with_implicit_vars(subst, motive),
        cases,
      )
    }
  }
}

// ============================================================================
// LITERAL TYPE UNIFICATION
// ============================================================================

/// Check if two literal type values can unify.
/// Overloaded integer types (ILitT) unify with any concrete integer or float type.
/// Overloaded float types (FLitT) unify with any concrete float type.
pub fn lit_types_unify(v1: ast.Value, v2: ast.Value) -> Bool {
  case v1, v2 {
    // Identical literal types always unify
    ast.VLitT(ast.I32T), ast.VLitT(ast.I32T) -> True
    ast.VLitT(ast.I64T), ast.VLitT(ast.I64T) -> True
    ast.VLitT(ast.U32T), ast.VLitT(ast.U32T) -> True
    ast.VLitT(ast.U64T), ast.VLitT(ast.U64T) -> True
    ast.VLitT(ast.F32T), ast.VLitT(ast.F32T) -> True
    ast.VLitT(ast.F64T), ast.VLitT(ast.F64T) -> True
    ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT) -> True
    ast.VLitT(ast.FLitT), ast.VLitT(ast.FLitT) -> True
    // Overloaded integer type resolves to any concrete integer or float type
    ast.VLitT(ast.ILitT), ast.VLitT(ast.I32T) -> True
    ast.VLitT(ast.ILitT), ast.VLitT(ast.I64T) -> True
    ast.VLitT(ast.ILitT), ast.VLitT(ast.U32T) -> True
    ast.VLitT(ast.ILitT), ast.VLitT(ast.U64T) -> True
    ast.VLitT(ast.ILitT), ast.VLitT(ast.F32T) -> True
    ast.VLitT(ast.ILitT), ast.VLitT(ast.F64T) -> True
    ast.VLitT(ast.I32T), ast.VLitT(ast.ILitT) -> True
    ast.VLitT(ast.I64T), ast.VLitT(ast.ILitT) -> True
    ast.VLitT(ast.U32T), ast.VLitT(ast.ILitT) -> True
    ast.VLitT(ast.U64T), ast.VLitT(ast.ILitT) -> True
    ast.VLitT(ast.F32T), ast.VLitT(ast.ILitT) -> True
    ast.VLitT(ast.F64T), ast.VLitT(ast.ILitT) -> True
    // Overloaded float type resolves to any concrete float type
    ast.VLitT(ast.FLitT), ast.VLitT(ast.F32T) -> True
    ast.VLitT(ast.FLitT), ast.VLitT(ast.F64T) -> True
    ast.VLitT(ast.F32T), ast.VLitT(ast.FLitT) -> True
    ast.VLitT(ast.F64T), ast.VLitT(ast.FLitT) -> True
    _, _ -> False
  }
}
