/// Type Inference — Bidirectional Type Checking
///
/// The `infer` module implements bidirectional type checking for the Core
/// language. Every term can be synthesized (inferred), and `check` is a
/// thin wrapper that synthesizes the term then unifies its type with
/// the expected type.

import core/ast.{type Value, type Term, type Case, type Pattern, VTypeDef, VCtr, VNeut, VErr, VPi, VRcd, VRcdT, VTyp, Var, Hole, Lam, App, Lit, Ctr, Match, Ann, Call, Rcd, RcdT, Typ, TypeDef, let_var, error_term, make_neut, make_hole_neut, make_var_neut, shift_term, shift_term_from, shift_opt, subst, type_of_type_def, find_constructor, compute_constructor_type, term_to_string, value_to_string}
import core/state.{FfiEntry}
import core/eval.{evaluate, match_pattern, match_type_pattern}
import core/subst.{force, force_levels_to_indices}
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
///
/// When checking a record literal against a record type with defaults,
/// fills in missing fields with the default values from the expected type.
pub fn check(
  state: state.State,
  term: ast.Term,
  expected: ast.Value,
) -> #(ast.Value, ast.Value, state.State) {
  // Fill in record defaults if checking a record against a record type
  let filled_term = fill_record_defaults(term, expected)
  let #(value, inferred, new_state) = infer(state, filled_term)
  unify_infer_and_check(new_state, value, inferred, expected)
}

/// Fill in missing record fields with defaults from the expected record type.
///
/// When the term is a record literal (`Rcd`) and the expected type is a
/// record type (`VRcdT`) with default values, this fills in any missing
/// fields with their defaults.
///
/// For example, checking `{x: 1}` against `${x: $Int, y: $Int = 0}` produces
/// `{x: 1, y: 0}` — the missing `y` field is filled with the default `0`.
fn fill_record_defaults(
  term: ast.Term,
  expected: ast.Value,
) -> ast.Term {
  case term, expected {
    ast.Rcd(fields, span), ast.VRcdT(expected_fields) -> {
      // Build a map of field name -> default value (if any)
      let defaults = build_defaults(expected_fields)
      // Fill in missing fields
      let filled = fill_fields(fields, defaults)
      case filled == fields {
        True -> term
        False -> ast.Rcd(filled, span)
      }
    }
    _, _ -> term
  }
}

/// Build a list of (name, default_term) pairs from a VRcdT's fields.
fn build_defaults(
  expected: List(#(String, ast.Value, option.Option(ast.Value))),
) -> List(#(String, ast.Term)) {
  list.fold(expected, [], fn(acc, field) {
    case field {
      #(_, _, Some(default_val)) ->
        [#(field.0, force_levels_to_indices(default_val, 0)), ..acc]
      _ -> acc
    }
  })
}

/// Fill in missing fields in a record with defaults.
fn fill_fields(
  fields: List(#(String, ast.Term)),
  defaults: List(#(String, ast.Term)),
) -> List(#(String, ast.Term)) {
  // Get the names of existing fields
  let existing_names = list.map(fields, fn(f) { f.0 })
  // Find defaults for fields not in existing
  let missing = list.filter(defaults, fn(d) {
    !list.contains(existing_names, d.0)
  })
  // Append missing fields to existing
  list.append(fields, missing)
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
  // Holes are synthesized to fresh hole values for both value and type.
  // Value and type get different fresh IDs so they don't unify trivially.
  let fresh_id_val = state.hole_counter
  let fresh_id_type = fresh_id_val + 1
  let new_state = state.State(..state, hole_counter: fresh_id_type + 1)
  let hole_val = ast.VNeut(ast.HHole(fresh_id_val), [])
  let hole_type = ast.VNeut(ast.HHole(fresh_id_type), [])
  #(hole_val, hole_type, new_state)
}

fn infer_lit(
  state: state.State,
  value: ast.Literal,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // The VALUE of a literal is the literal itself.
  // The TYPE of a literal is the type constructor ($Int or $Float).
  let literal_value = case value {
    ast.Int(v) -> ast.VLit(ast.Int(v))
    ast.Float(v) -> ast.VLit(ast.Float(v))
  }
  let literal_type = case value {
    ast.Int(_) -> ast.VLit(ast.Int(0))  // $Int
    ast.Float(_) -> ast.VLit(ast.Float(0.0))  // $Float
  }
  #(literal_value, literal_type, state)
}

/// Infer a type universe ($Type<n>).
/// $Type<n> evaluates to VTyp(n), with type VTyp(n+1).

fn infer_typ(
  state: state.State,
  level: Int,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let term_val = ast.VTyp(level)
  let type_val = ast.VTyp(level + 1)
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
  // Pi types are types, so their type is * (VTyp(0))
  #(pi_type, ast.VTyp(0), state)
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
  let #(field_vals, field_types, new_state) =
    infer_fields(state, fields, [], [])
  // Record {x: 1, y: 3.14} has type ${x: $Int, y: $Float}
  // field_types is List(#(String, Value)) - extract the Value part
  let rcd_type = ast.VRcdT(
    list.map2(fields, field_types, fn(f, t) {
      #(f.0, t.1, None)
    }),
  )
  #(ast.VRcd(field_vals), rcd_type, new_state)
}

/// Infer a record type: ${name: type, default?, ...}
fn infer_rcd_type(
  state: state.State,
  fields: List(#(String, ast.Term, option.Option(ast.Term))),
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // Evaluate each field's type annotation and optional default to values
  let #(field_vals, new_state) = infer_rcd_type_fields(state, fields, [], [])
  // Record type ${...} has type $Type<0> (VTyp(0))
  #(ast.VRcdT(field_vals), ast.VTyp(0), new_state)
}

/// Recursively infer record type fields with their optional defaults.
fn infer_rcd_type_fields(
  state: state.State,
  fields: List(#(String, ast.Term, option.Option(ast.Term))),
  acc: List(#(String, ast.Value, option.Option(ast.Value))),
  _types_acc: List(#(String, ast.Value)),
) -> #(
  List(#(String, ast.Value, option.Option(ast.Value))),
  state.State,
) {
  case fields {
    [] -> #(list.reverse(acc), state)
    [#(name, field_type, default), ..rest] -> {
      let #(field_val, _, state2) = infer(state, field_type)
      let default_val = case default {
        Some(d) -> Some(evaluate(state2, d))
        None -> None
      }
      infer_rcd_type_fields(
        state2,
        rest,
        [#(name, field_val, default_val), ..acc],
        [],
      )
    }
  }
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
  span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // Infer the argument to get both its value and type
  let #(arg_val, arg_type, state1) = infer(state, arg)

  // Look up constructor in env for GADT-style checking
  // Extract just the Value types from the env
  let env_values = list.map(state1.vars, fn(v) { v.1.0 })
  let constructor_info = lookup_constructor(env_values, tag)

  case constructor_info {
    Some(#(self_type_val, result_type_val, _)) -> {
      // Match argument type against self_type pattern
      let bindings = match_type_pattern(self_type_val, arg_type, [])

      case bindings {
        Some(env) -> {
          // Result_type_val is already evaluated, just use it
          let ctr_val = ast.VCtr(tag, arg_val)
          #(ctr_val, result_type_val, state1)
        }
        None -> {
          // Pattern mismatch: error + best-effort
          let new_state = state.State(
            ..state1,
            errors: [state.CtorArgTypeMismatch(tag, self_type_val, arg_type, span), ..state1.errors],
          )
          let ctr_val = ast.VCtr(tag, arg_val)
          let ctr_type = ast.VNeut(ast.HHole(0), [])
          #(ctr_val, ctr_type, new_state)
        }
      }
    }
    None -> {
      // Not a known constructor: fall back to current behavior
      let ctr_val = ast.VCtr(tag, arg_val)
      let ctr_type = ast.VCtr(tag, arg_type)
      #(ctr_val, ctr_type, state1)
    }
  }
}

fn infer_type_def(
  state: state.State,
  name: String,
  constructors: List(#(String, ast.Term, ast.Term, Span)),
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // Evaluate self_type and result_type terms for each constructor.
  // The self_type is evaluated to a value representing the pattern that
  // constructor arguments must match against.
  // The result_type is evaluated to a value representing the type of the
  // constructed value.
  let value_constructors = list.map(constructors, fn(c) {
    let tag = c.0
    let self_type_term = c.1
    let result_type_term = c.2
    let ctor_span = c.3
    // Evaluate self_type to a value
    let self_type_val = evaluate(state, self_type_term)
    // Evaluate result_type to a value (may contain holes for computed fields)
    let result_type_val = evaluate(state, result_type_term)
    #(tag, self_type_val, result_type_val, ctor_span)
  })
  let type_def_val = ast.VTypeDef(
    name: name,
    constructors: value_constructors,
  )
  // The type of a TypeDef is * (VTyp(0))
  #(type_def_val, ast.VTyp(0), state)
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

// ============================================================================
// GADT-STYLE CONSTRUCTOR CHECKING HELPERS
// ============================================================================

/// Look up a constructor tag across all TypeDefs in the env.
///
/// Searches through the env for VTypeDef values, then looks up
/// the constructor by tag. Returns the self_type value, result_type
/// value, and the VTypeDef if found.
fn lookup_constructor(
  env: List(Value),
  tag: String,
) -> Option(#(Value, Value, Value)) {
  case list.find(env, fn(v) {
    case v {
      VTypeDef(_, constructors) ->
        list.any(constructors, fn(c) { c.0 == tag })
      _ -> False
    }
  }) {
    Ok(VTypeDef(_, constructors)) -> {
      case list.find(constructors, fn(c) { c.0 == tag }) {
        Ok(#(_tag, self_type_val, result_type_val, _)) ->
          Some(#(self_type_val, result_type_val, VTypeDef(name: "", constructors: constructors)))
        Error(_) -> None
      }
    }
    _ -> None
  }
}

/// Evaluate a term with additional bindings in the env.
///
/// The bindings are short-lived — used only for this evaluation.
/// If evaluation fails, returns a hole as best-effort.
fn evaluate_with_bindings(state: state.State, term: ast.Term, bindings: List(#(String, ast.Value))) -> ast.Value {
  let new_vars = list.map(bindings, fn(b) { #(b.0, #(b.1, ast.VNeut(ast.HHole(0), []))) })
  let new_state = state.State(..state, vars: list.append(new_vars, state.vars))
  evaluate(new_state, term)
}
