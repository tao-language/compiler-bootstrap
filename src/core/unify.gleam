/// Unification — Higher-order unification for Core values.
///
/// Unification checks whether two `Value`s are "the same" and records
/// any mismatches as errors in the `State`. It also resolves holes
/// (unbound metavariables) by binding them to their types.
///
/// ## How it works
///
/// `unify(state, expected, actual)` recursively compares the two values:
///
/// - **Holes** (`VNeut(HHole(id))`) — unbound metavariables. When the
///   expected type is a hole, we bind it to the actual type in state.
///   An occur-check prevents binding a hole to a value containing itself.
/// - **Variables** (`VNeut(HVar(level))`) — compared structurally.
/// - **Same constructors** — recursively unify their fields.
/// - **Mismatched constructors** — record a `TypeMismatch` error.
///
/// Before comparing, both values are force-normalized via `force_value`
/// to resolve any already-solved holes. This ensures we compare
/// canonical forms.
///
/// The type checker calls this function at every place where two types
/// must agree. All errors accumulate in state; no early returns.
import core/ast
import core/eval
import core/state.{type FFI, type State, State, TypeMismatch, with_err}
import core/unwrap.{unwrap}
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span, Span}

pub fn unify(
  state: State,
  a: #(ast.Value, Span),
  b: #(ast.Value, Span),
) -> State {
  let #(value1, s1) = a
  let #(value2, s2) = b
  case value1, value2 {
    ast.VTyp(u1), ast.VTyp(u2) if u1 == u2 -> state
    ast.VLit(v1), ast.VLit(v2) if v1 == v2 -> state
    ast.VLitT(v1), ast.VLitT(v2) if v1 == v2 -> state
    ast.VCtr(t1, a1), ast.VCtr(t2, a2) if t1 == t2 ->
      unify(state, #(a1, s1), #(a2, s2))
    ast.VRcd(fields1), ast.VRcd(fields2) ->
      unify_rcd(state, fields1, fields2, s1)
    ast.VRcdT(fields1), ast.VRcdT(fields2) ->
      unify_rcd_type(state, fields1, fields2, s1)
    ast.VLam(i1, #(_, a1), #(env1, b1)), ast.VLam(i2, #(_, a2), #(env2, b2)) -> {
      // // Evaluate both bodies with their respective environments to get Values,
      // // then unify the resulting values.
      // // The param gets a dummy value of vvar(0, []), shifted to account for
      // // the env's existing binders.
      // let param_val = ast.vvar(0, [])
      // let shifted_param = shift.shift_value(param_val, list.length(env1))
      // let env1_with_param = list.append(env1, [shifted_param])
      // let body_val1 = eval_vlam_body(state.ffi, env1_with_param, body1)
      // let shifted_param2 = shift.shift_value(param_val, list.length(env2))
      // let env2_with_param = list.append(env2, [shifted_param2])
      // let body_val2 = eval_vlam_body(state.ffi, env2_with_param, body2)
      // unify_values(state, #(body_val1, span1), #(body_val2, span2))
      todo
    }
    ast.VPi(i1, #(_, a1), #(env1, b1)), ast.VPi(i2, #(_, a2), #(env2, b2)) -> {
      // let state = unify_string_value_pairs(state, imp1, imp2, span1)
      // let state = unify_values(state, #(dom1.1, span1), #(dom2.1, span2))
      // unify_values(state, #(cod1, span1), #(cod2, span2))
      todo
    }
    ast.VTypeDef(params1, ctrs1), ast.VTypeDef(params2, ctrs2) -> {
      todo
    }
    ast.VNeut(n1), ast.VNeut(n2) -> unify_neut(state, #(n1, s1), #(n2, s2))
    ast.VErr, ast.VErr -> state
    _, _ -> with_err(state, TypeMismatch(a, b))
  }
}

/// Unify two record field lists by name and type.
fn unify_rcd(
  state: State,
  fields1: List(#(String, ast.Value)),
  fields2: List(#(String, ast.Value)),
  span: Span,
) -> State {
  case fields1, fields2 {
    [], [] -> state
    [f1, ..rest1], [f2, ..rest2] -> {
      case f1.0 == f2.0 {
        True -> {
          let state = unify(state, #(f1.1, span), #(f2.1, span))
          unify_rcd(state, rest1, rest2, span)
        }
        False -> with_err(state, TypeMismatch(#(f1.1, span), #(f2.1, span)))
      }
    }
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VRcd(fields1), span), #(ast.VRcd(fields2), span)),
      )
  }
}

/// Unify two record type field lists by name and type.
fn unify_rcd_type(
  state: State,
  fields1: List(#(String, ast.Value, Option(ast.Value))),
  fields2: List(#(String, ast.Value, Option(ast.Value))),
  span: Span,
) -> State {
  case fields1, fields2 {
    [], [] -> state
    [f1, ..rest1], [f2, ..rest2] -> {
      case f1.0 == f2.0 {
        True -> {
          let state = unify(state, #(f1.1, span), #(f2.1, span))
          let state = unify_option_value(state, f1.2, f2.2, span)
          unify_rcd_type(state, rest1, rest2, span)
        }
        False -> with_err(state, TypeMismatch(#(f1.1, span), #(f2.1, span)))
      }
    }
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VRcdT(fields1), span), #(ast.VRcdT(fields2), span)),
      )
  }
}

/// Unify two optional values.
fn unify_option_value(
  state: State,
  opt1: Option(ast.Value),
  opt2: Option(ast.Value),
  span: Span,
) -> State {
  case opt1, opt2 {
    Some(v1), Some(v2) -> unify(state, #(v1, span), #(v2, span))
    None, None -> state
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VRcdT([#("x", ast.VErr, opt1)]), span), #(
          ast.VRcdT([#("x", ast.VErr, opt2)]),
          span,
        )),
      )
  }
}

fn unify_neut(
  state: State,
  a: #(ast.Neut, Span),
  b: #(ast.Neut, Span),
) -> State {
  todo
}
