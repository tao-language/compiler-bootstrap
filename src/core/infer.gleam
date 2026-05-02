/// Type Inference — Bidirectional Type Checking
///
/// The `infer` module implements bidirectional type checking for the Core
/// language. Every term can be synthesized (inferred), and `check` is a
/// thin wrapper that synthesizes the term then unifies its type with
/// the expected type.

import core/ast
import core/state.{FfiEntry}
import core/eval.{evaluate, match_pattern}
import core/subst.{force}
import core/unify.{unify}
import gleam/int
import gleam/list
import gleam/option.{type Option, Some, None}
import syntax/span.{type Span}

// ============================================================================
// PUBLIC API
// ============================================================================

/// Infer the type of a term (synthesis).
pub fn infer(state: state.State, term: ast.Term) -> #(ast.Value, ast.Value, state.State) {
  case term {
    ast.Var(index, span) -> infer_var(state, index, span)
    ast.Hole(id, span) -> infer_hole(state, id, span)
    ast.Lit(value, span) -> infer_lit(state, value, span)
    ast.Typ(level, span) -> infer_typ(state, level, span)
    ast.Lam(implicits, param, body, span) -> infer_lam(state, implicits, param, body, span)
    ast.Pi(implicits, domain, codomain, span) -> infer_pi(state, implicits, domain, codomain, span)
    ast.App(fun, arg, span) -> infer_app(state, fun, arg, span)
    ast.Ann(inner, type_, span) -> infer_ann(state, inner, type_, span)
    ast.Match(arg, cases, span) -> infer_match(state, arg, cases, span)
    ast.Call(name, args, typed_args, return_type, span) -> infer_call(state, name, args, typed_args, return_type, span)
    ast.Rcd(fields, span) -> infer_rcd(state, fields, span)
    ast.RcdT(fields, span) -> infer_rcd_type(state, fields, span)
    ast.Ctr(tag, arg, span) -> infer_ctr(state, tag, arg, span)
    ast.TypeDef(name, constructors, span) -> infer_type_def(state, name, constructors, span)
    ast.Err(message, span) -> infer_err(state, message, span)
  }
}

/// Check that a term has the expected type (verification).
pub fn check(
  state: state.State,
  term: ast.Term,
  expected: ast.Value,
) -> #(ast.Value, ast.Value, state.State) {
  let #(value, inferred, new_state) = infer(state, term)
  unify_infer_and_check(new_state, value, inferred, expected)
}

// ============================================================================
// SYNTHESIS — Figure out types
// ============================================================================

fn infer_var(
  state: state.State,
  index: Int,
  span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  case state.lookup_by_level(state, index) {
    Ok(#(value, type_)) -> #(value, type_, state)
    Error(_) -> {
      let new_state = state.with_err(
        state,
        state.VarUndefined("v@" <> int.to_string(index), span),
      )
      #(ast.VErr, ast.VErr, new_state)
    }
  }
}

fn infer_hole(
  state: state.State,
  _id: Int,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // Holes are synthesized to a fresh hole value
  let fresh_id = state.hole_counter
  let new_state = state.State(..state, hole_counter: fresh_id + 1)
  let hole_val = ast.VNeut(ast.HHole(fresh_id), [])
  #(hole_val, hole_val, new_state)
}

fn infer_lit(
  state: state.State,
  value: ast.Literal,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let literal_value = case value {
    ast.Int(v) -> ast.VLit(ast.Int(v))
    ast.Float(v) -> ast.VLit(ast.Float(v))
  }
  let literal_type = case value {
    ast.Int(v) -> ast.VLit(ast.Int(v))
    ast.Float(v) -> ast.VLit(ast.Float(v))
  }
  #(literal_value, literal_type, state)
}

/// Infer a numeric type reference ($Int, $Float, $I8, etc.).
/// These are type constructors that can be used in annotations.

fn infer_typ(
  state: state.State,
  level: Int,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let term_val = ast.VNeut(ast.HVar(level), [])
  let type_val = ast.VNeut(ast.HVar(level + 1), [])
  #(term_val, type_val, state)
}

fn infer_lam(
  state: state.State,
  implicits: List(#(String, ast.Term)),
  param: #(String, ast.Term),
  body: ast.Term,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let param_name = param.0
  let param_type_term = param.1
  let param_val = evaluate(state, param_type_term)

  // Evaluate implicits
  let implicit_env = list.map(implicits, fn(i) {
    let ival = evaluate(state, i.1)
    #(i.0, ival)
  })

  let bound_value = ast.VNeut(ast.HVar(0), [])
  let state_ext = state.State(
    ..state,
    vars: [#(param_name, #(bound_value, param_val)), ..state.vars],
  )

  let #(_body_val, body_type, state5) = infer(state_ext, body)

  let env = list.map(state.vars, fn(v) { v.1.0 })
  let lam_value = ast.VLam(env, implicit_env, #(param_name, param_val), body)
  let pi_type = ast.VPi(env, implicit_env, #(param_name, param_val), body_type)

  #(lam_value, pi_type, state5)
}

fn infer_pi(
  state: state.State,
  _implicits: List(#(String, ast.Term)),
  domain: #(String, ast.Term),
  codomain: ast.Term,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let dom_name = domain.0
  let dom_term = domain.1
  let dom_val = evaluate(state, dom_term)
  let codom_val = evaluate(state, codomain)
  let pi_type = ast.VPi([], [], #(dom_name, dom_val), codom_val)
  #(pi_type, ast.VNeut(ast.HVar(0), []), state)
}

fn infer_app(
  state: state.State,
  fun: ast.Term,
  arg: ast.Term,
  span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let #(fun_type, _, state2) = infer(state, fun)

  case fun_type {
    ast.VPi(_env, _implicits, domain, codomain) -> {
      let #(arg_val, _, state3) = check(state2, arg, domain.1)
      let _ = arg_val
      #(codomain, codomain, state3)
    }
    _other -> {
      let new_state = state.with_err(
        state,
        state.NotAFunction(fun_type, span),
      )
      #(ast.VErr, ast.VErr, new_state)
    }
  }
}

fn infer_ann(
  state: state.State,
  inner: ast.Term,
  type_: ast.Term,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let type_val = evaluate(state, type_)
  let #(value, _, state2) = check(state, inner, type_val)
  #(value, type_val, state2)
}

fn infer_match(
  state: state.State,
  arg: ast.Term,
  cases: List(ast.Case),
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let #(arg_val, arg_type, state2) = infer(state, arg)
  let #(result_val, result_type, final_state) =
    check_match_cases(state2, arg_val, arg_type, cases, [])

  // result_val is already the evaluated body of the matching case
  #(result_val, result_type, final_state)
}

fn check_match_cases(
  state: state.State,
  scrutinee_val: ast.Value,
  scrutinee_type: ast.Value,
  cases: List(ast.Case),
  acc: List(#(ast.Value, ast.Value)),
) -> #(ast.Value, ast.Value, state.State) {
  case cases {
    [] -> #(ast.VErr, ast.VErr, state)
    [ast.Case(pattern, _guard, body, _span), ..rest] -> {

      case match_pattern(pattern, scrutinee_val, []) {
        Ok(bindings) -> {
          let body_state = state.State(
            ..state,
            vars: list.map(bindings, fn(b) { #(b.0, #(b.1, ast.VNeut(ast.HHole(0), []))) }),
          )
          let #(body_val, body_type, state3) = check(body_state, body, scrutinee_type)

          let acc2 = list.append(acc, [#(body_val, body_type)])
          check_match_cases(state3, scrutinee_val, scrutinee_type, rest, acc2)
        }
        Error(_) -> {
          let #(body_val, body_type, state3) = check(state, body, scrutinee_type)
          let acc2 = list.append(acc, [#(body_val, body_type)])
          check_match_cases(state3, scrutinee_val, scrutinee_type, rest, acc2)
        }
      }
    }
  }
}

fn infer_call(
  state: state.State,
  name: String,
  args: List(ast.Term),
  typed_args: List(#(ast.Term, ast.Term)),
  return_type: Option(ast.Term),
  span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // If typed args are provided, validate them and use the return type if present
  let validated_args = case typed_args {
    [] -> args
    _ -> list.map(typed_args, fn(ta) { ta.0 })
  }
  case state.lookup_ffi(state, name) {
    Ok(FfiEntry(_fn_name, impl_fn)) -> {
      let eval_args = list.map(validated_args, fn(a) { evaluate(state, a) })
      let arg_types = list.map(eval_args, fn(_v) { ast.VNeut(ast.HHole(0), []) })
      let arg_pairs = list.map2(eval_args, arg_types, fn(v, t) { #(v, t) })
      let result = case impl_fn(arg_pairs) {
        Some(r) -> r
        None -> ast.VErr
      }
      // If return type is specified, check against it
      let result_type = case return_type {
        Some(rt) -> evaluate(state, rt)
        None -> result
      }
      #(result, result_type, state)
    }
    Error(_) -> {
      let new_state = state.with_err(
        state,
        state.CtrUndefined(name, span),
      )
      #(ast.VErr, ast.VErr, new_state)
    }
  }
}

fn infer_rcd(
  state: state.State,
  fields: List(#(String, ast.Term)),
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let #(field_vals, _field_types, new_state) =
    infer_fields(state, fields, [], [])
  #(ast.VRcd(field_vals), ast.VNeut(ast.HVar(0), []), new_state)
}

/// Infer a record type: ${name: type, ...
fn infer_rcd_type(
  state: state.State,
  fields: List(#(String, ast.Term, option.Option(ast.Term))),
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // Evaluate each field's type annotation to a value
  let type_fields = list.map(fields, fn(f) { #(f.0, f.1) })
  let #(field_vals, _, new_state) =
    infer_fields(state, type_fields, [], [])
  // Record type evaluates to a neutral value representing the type
  #(ast.VRcd(field_vals), ast.VNeut(ast.HVar(0), []), new_state)
}

fn infer_fields(
  state: state.State,
  fields: List(#(String, ast.Term)),
  vals_acc: List(#(String, ast.Value)),
  types_acc: List(#(String, ast.Value)),
) -> #(List(#(String, ast.Value)), List(#(String, ast.Value)), state.State) {
  case fields {
    [] -> #(list.reverse(vals_acc), list.reverse(types_acc), state)
    [#(name, field), ..rest] -> {
      let #(field_val, field_type, state2) = infer(state, field)
      infer_fields(
        state2,
        rest,
        [#(name, field_val), ..vals_acc],
        [#(name, field_type), ..types_acc],
      )
    }
  }
}

fn infer_ctr(
  state: state.State,
  tag: String,
  arg: ast.Term,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let arg_val = evaluate(state, arg)
  let ctr_val = ast.VCtr(tag, arg_val)
  #(ctr_val, ast.VNeut(ast.HVar(0), []), state)
}

fn infer_type_def(
  state: state.State,
  name: String,
  constructors: List(#(String, ast.Term, ast.Term, Span)),
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // Convert Term-level TypeDef to VTypeDef value
  // For now, we just wrap constructors in neutral values
  let value_constructors = list.map(constructors, fn(c) {
    let tag = c.0
    let ctor_span = c.3
    #(tag, ast.VNeut(ast.HHole(0), []), ast.VNeut(ast.HHole(0), []), ctor_span)
  })
  let type_def_val = ast.VTypeDef(
    name: name,
    constructors: value_constructors,
  )
  // The type of a TypeDef is *
  let type_def_type = ast.VPi(
    [],
    [],
    #("_", ast.VLit(ast.Int(0))),
    ast.VPi(
      [],
      [],
      #("_", ast.VLit(ast.Int(1))),
      type_def_val,
    ),
  )
  #(type_def_val, type_def_type, state)
}

fn infer_err(
  state: state.State,
  _message: String,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  #(ast.VErr, ast.VErr, state)
}

// ============================================================================
// UNIFICATION HELPER
// ============================================================================

fn unify_infer_and_check(
  state: state.State,
  value: ast.Value,
  inferred_type: ast.Value,
  expected_type: ast.Value,
) -> #(ast.Value, ast.Value, state.State) {
  case inferred_type, expected_type {
    ast.VErr, _ | _, ast.VErr -> #(ast.VErr, ast.VErr, state)
    _, _ -> {
      let state = unify(state, expected_type, inferred_type)
      let forced = force(state, value)
      let forced_type = force(state, inferred_type)
      #(forced, forced_type, state)
    }
  }
}
