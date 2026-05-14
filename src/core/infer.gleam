/// Type Inference — Bidirectional Type Checking
///
/// The `infer` module implements bidirectional type checking for the Core
/// language. Every term can be synthesized (inferred), and `check` is a
/// thin wrapper that synthesizes the term then unifies its type with
/// the expected type.

import core/ast.{type Value, type Term,
  VTypeDef,
  IntT, FloatT}
import core/exhaustiveness.{check_exhaustiveness_vdef}
import core/state.{FfiEntry, def_var, env_to_state, type State, State}
import core/eval.{evaluate, match_pattern}
import core/subst.{force, force_levels_to_indices, subst_term_var}
import core/unify.{unify}
import gleam/float
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
    ast.Call(name, args, return_type, span) -> infer_call(state, name, args, return_type, span)
    ast.Rcd(fields, span) -> infer_rcd(state, fields, span)
    ast.RcdT(fields, span) -> infer_rcd_type(state, fields, span)
    ast.Ctr(tag, arg, span) -> infer_ctr(state, tag, arg, span)
    ast.TypeDef(name, params, constructors, span) -> infer_type_def(state, name, params, constructors, span)
    ast.Err(message, span) -> infer_err(state, message, span)
    ast.LitT(t, span) -> infer_litt(state, t, span)
    ast.Fix(name, body, span) -> infer_fix(state, name, body, span)
  }
}

/// Infer a pattern against an expected type (synthesis).
///
/// Validates that the pattern matches the expected type and returns
/// the pattern bindings for use in the match body. This is used when
/// the scrutinee type is not a TypeDef (so we can't do structural
/// exhaustiveness checking) — we synthesize the pattern's type instead.
///
/// For patterns that are TypeDef-aware, use `check_pattern` instead.
pub fn infer_pattern(
  state: state.State,
  pattern: ast.Pattern,
  expected_type: ast.Value,
) -> #(List(#(String, ast.Value)), state.State) {
  check_pattern(state, pattern, expected_type)
}

/// Check a pattern against an expected type (verification).
///
/// Validates that the pattern matches the expected type and returns
/// the pattern bindings for use in the match body.
///
/// ## Pattern matching rules
///
/// - **PAny**: matches anything, no bindings
/// - **PVar**: matches anything, binds variable
/// - **PCtr**: matches constructor, recursively checks inner pattern
/// - **PUnit**: matches empty record type
/// - **PLit**: matches literal type (IntT or FloatT)
/// - **PAlias**: delegates to inner pattern, adds alias binding
/// - **PType**: matches type universes
/// - **PRcd**: matches record type fields
/// - **PError**: matches error values
pub fn check_pattern(
  state: state.State,
  pattern: ast.Pattern,
  expected_type: ast.Value,
) -> #(List(#(String, ast.Value)), state.State) {
  check_pattern_inner(state, pattern, expected_type, [])
}

fn check_pattern_inner(
  state: state.State,
  pattern: ast.Pattern,
  expected_type: ast.Value,
  acc: List(#(String, ast.Value)),
) -> #(List(#(String, ast.Value)), state.State) {
  case pattern {
    ast.PAny(_) ->
      #(acc, state)

    ast.PVar(name, _) -> {
      // PVar matches anything; bind to a fresh hole
      let fresh_id = state.hole_counter
      let new_state = state.State(..state, hole_counter: fresh_id + 1)
      let hole_val = ast.VNeut(ast.HHole(fresh_id), [])
      let bindings = [#(name, hole_val), ..acc]
      #(bindings, new_state)
    }

    ast.PCtr(tag, inner, _) -> {
      // Look up the constructor in the env to get its expected argument type
      let env_values = list.map(state.vars, fn(v) { v.1.0 })
      let constructor_info = lookup_constructor(env_values, tag)

      case constructor_info {
        Some(#(_bindings, self_type_val, _result_type_val)) -> {
          // Constructor found: check inner pattern against self_type
          let inner_bindings = check_pattern(
            state,
            inner,
            self_type_val,
          )
          let bindings = list.append(inner_bindings.0, acc)
          #(bindings, inner_bindings.1)
        }
        None -> {
          // Constructor not found: fall back to matching anything
          let fresh_id = state.hole_counter
          let new_state = state.State(..state, hole_counter: fresh_id + 1)
          let hole_val = ast.VNeut(ast.HHole(fresh_id), [])
          let bindings = [#(tag, hole_val), ..acc]
          let inner_bindings = check_pattern(
            new_state,
            inner,
            ast.VNeut(ast.HHole(fresh_id), []),
          )
          let bindings = list.append(inner_bindings.0, bindings)
          #(bindings, inner_bindings.1)
        }
      }
    }

    ast.PUnit(_) -> {
      // PUnit matches empty record types
      case expected_type {
        ast.VRcdT(fields) -> {
          case fields {
            [] -> #(acc, state)
            _ -> #(acc, state)  // Best effort: allow non-empty
          }
        }
        _ -> {
          // Not a record type: allow it (best effort)
          #(acc, state)
        }
      }
    }

    ast.PLit(lit, _) -> {
      // PLit matches literal types (IntT, FloatT)
      case expected_type {
        ast.VLitT(ast.IntT) -> {
          case lit {
            ast.Int(_) -> #(acc, state)
            _ -> #(acc, state)  // Best effort: allow mismatch
          }
        }
        ast.VLitT(ast.FloatT) -> {
          case lit {
            ast.Float(_) -> #(acc, state)
            _ -> #(acc, state)  // Best effort: allow mismatch
          }
        }
        ast.VLitT(_) -> #(acc, state)  // Other literal types: allow
        _ -> #(acc, state)  // Non-literal type: allow
      }
    }

    ast.PAlias(name, inner, _) -> {
      // PAlias: bind the alias name, then delegate to inner pattern
      let inner_bindings = check_pattern(
        state,
        inner,
        expected_type,
      )
      // Add the alias binding (pointing to the first inner binding if available)
      let alias_val = case inner_bindings.0 {
        [first, .._] -> first.1
        [] -> ast.VNeut(ast.HHole(0), [])
      }
      let bindings = list.append(list.append(inner_bindings.0, [#(name, alias_val)]), acc)
      #(bindings, inner_bindings.1)
    }

    ast.PTyp(_type_name, _) -> {
      // PType matches type universes
      case expected_type {
        ast.VTyp(level) -> #(acc, state)
        ast.VLitT(ast.IntT) -> {
          // $Int wildcard: matches any integer type
          #(acc, state)
        }
        ast.VLitT(ast.FloatT) -> {
          // $Float wildcard: matches any float type
          #(acc, state)
        }
        _ -> #(acc, state)  // Best effort: allow
      }
    }

    ast.PRcd(fields, _) -> {
      // PRcd: match record type fields
      case expected_type {
        ast.VRcdT(expected_fields) -> {
          let fields_result = check_rcd_fields(fields, expected_fields, state, acc)
          #(fields_result.0, fields_result.1)
        }
        _ -> #(acc, state)  // Non-record type: allow
      }
    }

    ast.PLitT(lit_type, _) -> {
      // PLitT matches literal type values (e.g., $Int, $Float)
      case expected_type {
        ast.VLitT(t) ->
          case t == lit_type {
            True -> #(acc, state)
            False -> #(acc, state)  // Best effort: allow mismatch
          }
        _ -> #(acc, state)  // Non-literal type: allow
      }
    }

    ast.PError(_) -> {
      // PError matches error values
      case expected_type {
        ast.VErr -> #(acc, state)
        _ -> #(acc, state)  // Best effort: allow
      }
    }
  }
}

/// Check record pattern fields against expected record type fields.
fn check_rcd_fields(
  fields: List(#(String, ast.Pattern)),
  expected_fields: List(#(String, ast.Value, option.Option(ast.Value))),
  state: state.State,
  acc: List(#(String, ast.Value)),
) -> #(List(#(String, ast.Value)), state.State) {
  case fields {
    [] -> #(acc, state)
    [#(name, inner_pattern), ..rest] -> {
      case list.find(expected_fields, fn(f) { f.0 == name }) {
        Ok(#(_, field_type, _)) -> {
          let inner_result = check_pattern(
            state,
            inner_pattern,
            field_type,
          )
          check_rcd_fields(
            rest,
            expected_fields,
            inner_result.1,
            list.append(inner_result.0, acc),
          )
        }
        Error(_) -> {
          // Field not in expected type: allow (best effort)
          check_rcd_fields(
            rest,
            expected_fields,
            state,
            acc,
          )
        }
      }
    }
  }
}

/// Infer a fixpoint (recursive function) term.
///
/// A fixpoint term represents a recursive function defined via the Y combinator.
/// The term is `Fix(name, body)` where body is a lambda that takes the
/// recursive reference as an implicit parameter.
///
/// For example, a recursive factorial:
/// ```
/// $let fact = $fix(f) => $fn(n: $Int) => ...
/// ```
/// Desugars to: `Fix("fact", Lam([], body))`
///
/// The inferred type wraps the body's type in a Pi (the recursive function type).
pub fn infer_fix(
  state: state.State,
  name: String,
  body: ast.Term,
  span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // Bind `f` with a fresh hole so references to `f` within the body
  // can be resolved during inference. The hole acts as a placeholder
  // that inference will solve into a Pi type.
  let fresh_id = state.hole_counter
  let hole_ref = ast.VNeut(ast.HHole(fresh_id), [])
  let bound_value = ast.VNeut(ast.HVar(0), [])
  let state_bound = State(..state, hole_counter: fresh_id + 1,
    vars: [#(name, #(bound_value, hole_ref)), ..state.vars],
  )

  // Infer the body with `f` bound in the environment.
  let #(body_val, body_type, state2) = infer(state_bound, body)
  let _ = body_val

  // Shift body by -1 so `f` (Var(2) after term_to_debruijn due to pattern
  // variable shadowing) becomes Var(1) relative to the VLam's parameter.
  let shifted_body = ast.shift_term_from(body, -1, 1)

  let fix_value = ast.VFix(
    name,
    [bound_value],
    shifted_body,
  )

  let fix_type = ast.VPi(
    [],
    [],
    #(name, body_type),
    body_type,
  )

  #(fix_value, fix_type, state2)
}

/// Check that a term has the expected type (verification).
///
/// This is a thin wrapper: infer the term, then fill in any missing
/// record defaults at the value level before unifying.
pub fn check(
  state: state.State,
  term: ast.Term,
  expected: ast.Value,
) -> #(ast.Value, ast.Value, state.State) {
  let #(value, inferred, new_state) = infer(state, term)
  // Fill in missing record defaults at the value level
  let filled_value = fill_record_defaults_value(value, expected)
  unify_infer_and_check(new_state, filled_value, inferred, expected)
}

/// Fill in missing record fields with defaults at the value level.
///
/// When the value is a `VRcd` and the expected type is a `VRcdT`
/// with default values, this fills in any missing fields with their defaults.
///
/// For example, checking `VRcd([#("x", VLit(Int(1)))])` against
/// `VRcdT([#("x", VLitT(IntT), Some(VLitT(IntT))), #("y", VLitT(IntT), Some(VLit(42)))])`
/// produces `VRcd([#("x", VLit(Int(1))), #("y", VLit(42))])`.
fn fill_record_defaults_value(
  value: ast.Value,
  expected: ast.Value,
) -> ast.Value {
  case value, expected {
    ast.VRcd(fields), ast.VRcdT(expected_fields) -> {
      // Build a map of field name -> default value
      let defaults = build_defaults_value(expected_fields)
      // Fill in missing fields
      let filled = fill_fields_value(fields, defaults)
      ast.VRcd(filled)
    }
    _, _ -> value
  }
}

/// Build a list of (name, default_value) pairs from a VRcdT's fields.
fn build_defaults_value(
  fields: List(#(String, ast.Value, option.Option(ast.Value))),
) -> List(#(String, ast.Value)) {
  list.fold(fields, [], fn(acc, field) {
    case field {
      #(_, _, Some(default_val)) -> [#(field.0, default_val), ..acc]
      _ -> acc
    }
  })
}

/// Fill in missing fields in a record with defaults at the value level.
fn fill_fields_value(
  fields: List(#(String, ast.Value)),
  defaults: List(#(String, ast.Value)),
) -> List(#(String, ast.Value)) {
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
  // The TYPE of a literal is the literal type: $Int for integers, $Float for floats.
  let literal_value = case value {
    ast.Int(v) -> ast.VLit(ast.Int(v))
    ast.Float(v) -> ast.VLit(ast.Float(v))
  }
  let literal_type = case value {
    ast.Int(_) -> ast.VLitT(IntT)  // $Int
    ast.Float(_) -> ast.VLitT(FloatT)  // $Float
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
  // Check if this is a $let binding: App(Lam(name, _, body), value, span)
  // If so, infer the arg, fill defaults at value level, add to env, infer body.
  case fun {
    ast.Lam(_implicits, #(param_name, param_type), body, _lam_span) -> {
      // Infer the argument to get its value and type
      let #(arg_val, arg_type, state2) = infer(state, arg)
      // Evaluate the parameter type to get the expected value type
      let param_val = evaluate(state2, param_type)
      // Fill in record defaults at the value level
      let filled_arg = fill_record_defaults_value(arg_val, param_val)
      // Int→Float conversion if param type is FloatT
      let converted_arg = case param_val {
        ast.VLitT(ast.FloatT) ->
          case filled_arg {
            ast.VLit(ast.Int(v)) ->
              case float.parse(int.to_string(v) <> ".0") {
                Ok(f) -> ast.VLit(ast.Float(f))
                Error(_) -> filled_arg
              }
            _ -> filled_arg
          }
        _ -> filled_arg
      }
      let state_ext = def_var(state2, param_name, converted_arg, arg_type)
      // Infer the body with the binding in the env
      let #(body_val, body_type, state_final) = infer(state_ext, body)
      #(body_val, body_type, state_final)
    }
    _ -> {
      // Normal function application: infer both fun and arg
      let #(fun_val, fun_type, state2) = infer(state, fun)
      let #(arg_val, arg_type, state3) = infer(state2, arg)

      // Try to normalize via beta reduction
      case fun_val {
        // β-reduction: apply VLam to argument
        ast.VLam(lam_env, _implicits, #(_pname, param_type), body) -> {
          // Fill defaults if param_type is VRcdT
          let filled_arg = fill_record_defaults_value(arg_val, param_type)
          // Int→Float conversion if param type is FloatT
          let converted_arg = case param_type {
            ast.VLitT(ast.FloatT) ->
              case filled_arg {
                ast.VLit(ast.Int(v)) ->
                  case float.parse(int.to_string(v) <> ".0") {
                    Ok(f) -> ast.VLit(ast.Float(f))
                    Error(_) -> filled_arg
                  }
                _ -> filled_arg
              }
            _ -> filled_arg
          }
          // Extend env with the lambda parameter
          let env_with_param = list.append([converted_arg], lam_env)
          let substituted = ast.shift_term(
            subst_term_var(0, converted_arg, body),
            1,
          )
          // Infer the body in the extended environment
          let body_state = env_to_state(env_with_param, state3.truth_ctr, state3.ffi)
          infer(body_state, substituted)
        }
        // VFix unroll: substitute arg for Var(0), VFix for Var(1)
        ast.VFix(fix_name, fix_env, fix_body) -> {
          let body = case fix_body {
            ast.Ann(inner, _, _) -> inner
            _ -> fix_body
          }
          case body {
            ast.Lam(_implicits, _param, body_term, _) -> {
              let body_with_arg = subst_term_var(0, arg_val, body_term)
              let self = ast.VFix(fix_name, fix_env, fix_body)
              let body_with_self = subst_term_var(1, self, body_with_arg)
              let env_with_arg = list.append([arg_val], fix_env)
              let body_state = env_to_state(env_with_arg, state3.truth_ctr, state3.ffi)
              infer(body_state, body_with_self)
            }
            _ -> #(ast.VErr, ast.VErr, state3)
          }
        }
        // Neutral spine: extend with argument
        ast.VNeut(head, spine) -> {
          let new_neut = ast.VNeut(head, list.append(spine, [ast.EApp(arg_val)]))
          #(new_neut, fun_type, state3)
        }
        // Error propagates
        ast.VErr -> #(ast.VErr, ast.VErr, state3)
        // Cannot apply a type/value that isn't a function
        _ -> {
          let new_state = state.with_err(
            state,
            state.NotAFunction(fun_type, span),
          )
          #(ast.VErr, ast.VErr, new_state)
        }
      }
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
  span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let #(arg_val, arg_type, state2) = infer(state, arg)
  let #(result_val, result_type, final_state) =
    check_match_cases(state2, arg_val, arg_type, cases, [])

  // Check exhaustiveness if the scrutinee type is a TypeDef
  let final_state = case arg_type {
    VTypeDef(name: _, params: _, constructors: constructors) -> {
      let covered_tags = collect_covered_tags(cases, arg_val)
      check_exhaustiveness_vdef(final_state, constructors, covered_tags, span)
    }
    _ -> final_state
  }

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
          // Pattern matched: evaluate the body and return immediately
          let body_state = state.State(
            ..state,
            vars: list.map(bindings, fn(b) { #(b.0, #(b.1, ast.VNeut(ast.HHole(0), []))) }),
          )
          check(body_state, body, scrutinee_type)
        }
        Error(_) -> {
          // Pattern didn't match: try next case
          check_match_cases(state, scrutinee_val, scrutinee_type, rest, acc)
        }
      }
    }
  }
}

/// Collect constructor tags covered by patterns in a list of cases.
///
/// This is used for exhaustiveness checking — we track which constructor
/// tags have been matched by at least one pattern.
fn collect_covered_tags(
  cases: List(ast.Case),
  _scrutinee_val: ast.Value,
) -> List(String) {
  cases
  |> list.fold([], fn(acc, c) {
    let tags = extract_tags_from_pattern(c.pattern)
    list.append(acc, tags)
  })
}

/// Extract constructor tags from a pattern.
///
/// Returns a list of tags that this pattern covers. For constructor
/// patterns (`#Tag(...)`), returns `["Tag"]`. For wildcard patterns
/// (`_`), returns an empty list (wildcards don't cover specific tags).
/// For record patterns, returns tags from inner constructor patterns.
fn extract_tags_from_pattern(pattern: ast.Pattern) -> List(String) {
  case pattern {
    ast.PAny(_) -> []
    ast.PVar(_, _) -> []
    ast.PAlias(_, inner, _) -> extract_tags_from_pattern(inner)
    ast.PCtr(tag, _, _) -> [tag]
    ast.PUnit(_) -> []
    ast.PLit(_, _) -> []
    ast.PLitT(_, _) -> []
    ast.PTyp(_, _) -> []
    ast.PRcd(fields, _) ->
      fields
      |> list.map(fn(f) { extract_tags_from_pattern(f.1) })
      |> list.flatten
    ast.PError(_) -> []
  }
}

fn infer_call(
  state: state.State,
  name: String,
  args: List(#(ast.Term, ast.Term)),
  return_type: ast.Term,
  span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // Evaluate each (value_term, type_term) pair
  let arg_vals = list.map(args, fn(ta) { evaluate(state, ta.0) })
  let arg_types = list.map(args, fn(ta) { evaluate(state, ta.1) })
  let arg_pairs = list.map2(arg_vals, arg_types, fn(v, t) { #(v, t) })

  // Evaluate return type
  let ret_type_val = evaluate(state, return_type)

  case state.lookup_ffi(state, name) {
    Ok(FfiEntry(_fn_name, impl_fn)) ->
      case impl_fn(arg_pairs) {
        Some(r) -> #(r, ret_type_val, state)
        None -> {
          // FFI couldn't evaluate (not concrete enough) — defer to runtime
          let vcall = ast.VCall(name, arg_pairs, ret_type_val)
          #(vcall, ret_type_val, state)
        }
      }
    Error(_) -> {
      // FFI not found — defer to runtime (will fail at runtime if not defined)
      // Also record the error for diagnostics
      let new_state = state.with_err(
        state,
        state.CtrUndefined(name, span),
      )
      let vcall = ast.VCall(name, arg_pairs, ret_type_val)
      #(vcall, ret_type_val, new_state)
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
    Some(#(_bindings, self_type_val, result_type_val)) -> {
      // self_type is a Value, result_type is a Term.
      // Type params (from TypeDef params) are referenced by name in the pattern.
      // Constructor-bound vars (@m) are also free variables.
      // For now, we treat them as-is - the unification will solve for free vars.

      // Unify argument type against self_type pattern
      // The self_type may contain VNeut(HVar(...), []) as unification variables
      let unified = unify_type_pattern(self_type_val, arg_type, [])

      case unified {
        Some(solved_bindings) -> {
          // Unification succeeded: substitute solved bindings into result_type (Term)
          // Then infer the result_type Term to get its Value
          let result_term = apply_unify_bindings_to_term(solved_bindings, result_type_val)
          let #(result_val, result_type_val2, _) = infer(state1, result_term)
          let ctr_val = ast.VCtr(tag, arg_val)
          #(ctr_val, result_type_val2, state1)
        }
        None -> {
          // Unification failed: error + best-effort
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
  params: List(#(String, ast.Term)),
  constructors: List(#(String, #(List(String), ast.Term, ast.Term), Span)),
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // Evaluate type params to values and bind them as fresh holes.
  // This ensures that type parameter references in self_type and result_type
  // resolve to the *same* hole for the same parameter name, enabling proper
  // unification during GADT constructor checking.
  //
  // For example, in `Option<a> { #Some(a) -> #Option(a) }`, the `a` in both
  // self_type and result_type must be the same unification variable.
  let #(hole_bindings, new_state) = list.fold(
    params,
    #( [], state ),
    fn(acc, p) {
      let #(acc_bindings, s) = acc
      let fresh_id = s.hole_counter
      let new_state = state.State(..s, hole_counter: fresh_id + 1)
      let _param_val = evaluate(new_state, p.1)
      let hole = ast.VNeut(ast.HHole(fresh_id), [])
      let updated_state = def_var(new_state, p.0, hole, hole)
      #([#(p.0, hole), ..acc_bindings], updated_state)
    },
  )

  // Process self_type and result_type terms for each constructor.
  // Since type params are now bound as holes in the environment, any
  // free variable references (like `a` in `#Some(a)`) resolve to the
  // corresponding bound hole. This ensures both self_type and result_type
  // use the same hole for the same type parameter.
  //
  // Note: De Bruijn indices in the type def body terms need to be shifted
  // by -(num_type_params) because the type params are at the front of the
  // state vars, and parser-level bindings are not present in the state.
  let num_type_params = list.length(params)
  let value_constructors = list.map(constructors, fn(c) {
    let #(tag, #(bindings, self_type_term, result_type_term), ctor_span) = c
    // Shift De Bruijn indices by -(num_type_params) to account for type
    // params being at the front of state vars (parser-level bindings are
    // not present in the state).
    let shifted_self = ast.shift_term(self_type_term, -num_type_params)
    let shifted_result = ast.shift_term(result_type_term, -num_type_params)
    // Evaluate self_type to a value (type params resolve to bound holes)
    let self_type_val = evaluate(new_state, shifted_self)
    // Keep result_type as a Term (not evaluated) so inference can evaluate it later
    #(tag, #(bindings, self_type_val, shifted_result), ctor_span)
  })

  // Keep type param bindings in vars so subsequent lambdas can reference them
  // via their implicit parameters (e.g., $fn<a: $Type>(expr: #Expr(a))).
  // The type params are at positions 0..n in vars; they will be shadowed
  // by outer let bindings if names collide, but that's correct behavior.
  let clean_state = new_state

  // value_params are the evaluated type parameter values (holes)
  // hole_bindings is in reverse order, so reverse it back
  let value_params = list.reverse(hole_bindings)
  let type_def_val = ast.VTypeDef(
    name: name,
    params: value_params,
    constructors: value_constructors,
  )
  // The type of a TypeDef is * (VTyp(0))
  #(type_def_val, ast.VTyp(0), clean_state)
}
fn infer_err(
  state: state.State,
  _message: String,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  #(ast.VErr, ast.VErr, state)
}

/// Infer a literal type annotation ($Int, $Float, $I32, etc.).
/// The value is the literal type itself (e.g., $Int), and its type is $Type<0>.
fn infer_litt(
  state: state.State,
  type_: ast.LiteralType,
  _span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  let value = ast.VLitT(type_)
  let type_val = ast.VTyp(0)
  #(value, type_val, state)
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
      // Apply literal type coercion based on expected type.
      // This handles Int→Float, Int→IXX/UXX, Float→FXX conversions.
      let #(converted_value, converted_type) = case value, expected_type {
        // Int literal → FloatT: convert to float
        ast.VLit(ast.Int(v)), ast.VLitT(ast.FloatT) ->
          case float.parse(int.to_string(v) <> ".0") {
            Ok(f) -> #(ast.VLit(ast.Float(f)), ast.VLitT(ast.FloatT))
            Error(_) -> #(value, inferred_type)
          }
        // Int literal → FXX: convert to float
        ast.VLit(ast.Int(v)), ast.VLitT(ast.F16T) ->
          #(ast.VLit(ast.Float(int.to_float(v))), ast.VLitT(ast.F16T))
        ast.VLit(ast.Int(v)), ast.VLitT(ast.F32T) ->
          #(ast.VLit(ast.Float(int.to_float(v))), ast.VLitT(ast.F32T))
        ast.VLit(ast.Int(v)), ast.VLitT(ast.F64T) ->
          #(ast.VLit(ast.Float(int.to_float(v))), ast.VLitT(ast.F64T))
        // Int literal → IXX/UXX: keep int, update type
        ast.VLit(ast.Int(v)), ast.VLitT(ast.I8T) ->
          #(ast.VLit(ast.Int(v)), ast.VLitT(ast.I8T))
        ast.VLit(ast.Int(v)), ast.VLitT(ast.I16T) ->
          #(ast.VLit(ast.Int(v)), ast.VLitT(ast.I16T))
        ast.VLit(ast.Int(v)), ast.VLitT(ast.I32T) ->
          #(ast.VLit(ast.Int(v)), ast.VLitT(ast.I32T))
        ast.VLit(ast.Int(v)), ast.VLitT(ast.I64T) ->
          #(ast.VLit(ast.Int(v)), ast.VLitT(ast.I64T))
        ast.VLit(ast.Int(v)), ast.VLitT(ast.U8T) ->
          #(ast.VLit(ast.Int(v)), ast.VLitT(ast.U8T))
        ast.VLit(ast.Int(v)), ast.VLitT(ast.U16T) ->
          #(ast.VLit(ast.Int(v)), ast.VLitT(ast.U16T))
        ast.VLit(ast.Int(v)), ast.VLitT(ast.U32T) ->
          #(ast.VLit(ast.Int(v)), ast.VLitT(ast.U32T))
        ast.VLit(ast.Int(v)), ast.VLitT(ast.U64T) ->
          #(ast.VLit(ast.Int(v)), ast.VLitT(ast.U64T))
        // Float literal → FXX: keep float, update type
        ast.VLit(ast.Float(v)), ast.VLitT(ast.F16T) ->
          #(ast.VLit(ast.Float(v)), ast.VLitT(ast.F16T))
        ast.VLit(ast.Float(v)), ast.VLitT(ast.F32T) ->
          #(ast.VLit(ast.Float(v)), ast.VLitT(ast.F32T))
        ast.VLit(ast.Float(v)), ast.VLitT(ast.F64T) ->
          #(ast.VLit(ast.Float(v)), ast.VLitT(ast.F64T))
        // Float literal → IntT/IXX/UXX: type error (handled by unify)
        ast.VLit(ast.Float(_)), ast.VLitT(ast.IntT) ->
          #(value, inferred_type)
        ast.VLit(ast.Float(_)), ast.VLitT(ast.I8T) ->
          #(value, inferred_type)
        ast.VLit(ast.Float(_)), ast.VLitT(ast.I16T) ->
          #(value, inferred_type)
        ast.VLit(ast.Float(_)), ast.VLitT(ast.I32T) ->
          #(value, inferred_type)
        ast.VLit(ast.Float(_)), ast.VLitT(ast.I64T) ->
          #(value, inferred_type)
        ast.VLit(ast.Float(_)), ast.VLitT(ast.U8T) ->
          #(value, inferred_type)
        ast.VLit(ast.Float(_)), ast.VLitT(ast.U16T) ->
          #(value, inferred_type)
        ast.VLit(ast.Float(_)), ast.VLitT(ast.U32T) ->
          #(value, inferred_type)
        ast.VLit(ast.Float(_)), ast.VLitT(ast.U64T) ->
          #(value, inferred_type)
        // Int literal → IntT: keep as is
        ast.VLit(ast.Int(_)), ast.VLitT(ast.IntT) ->
          #(value, inferred_type)
        // Float literal → FloatT: keep as is
        ast.VLit(ast.Float(_)), ast.VLitT(ast.FloatT) ->
          #(value, inferred_type)
        // Wildcard types: let unify handle it
        _, ast.VLitT(_) -> #(value, inferred_type)
        // Non-literal types: no conversion
        _, _ -> #(value, inferred_type)
      }
      let #( _, s1) = unify(state, expected_type, converted_type, infer)
      let state = s1
      let forced = force([], converted_value, dummy_do_match)
      let forced_type = force([], converted_type, dummy_do_match)
      #(forced, forced_type, state)
    }
  }
}

// ============================================================================
// GADT-STYLE CONSTRUCTOR CHECKING HELPERS
// ============================================================================

/// Find a TypeDef by looking up a constructor tag in the environment.
///
/// If the value is a VCtr(tag, arg), search through the env for VTypeDef
/// values that contain a constructor with the given tag. Returns
/// Some(#(type_def, arg)) if found, None otherwise.
pub fn find_type_def(
  env: List(Value),
  value: Value,
) -> Option(#(Value, Value)) {
  case value {
    ast.VCtr(tag, arg) -> {
      // Search through env for a VTypeDef containing this constructor
      case list.find(env, fn(v) {
        case v {
          ast.VTypeDef(_, _, constructors) ->
            list.any(constructors, fn(c) { c.0 == tag })
          _ -> False
        }
      }) {
        Ok(type_def) -> Some(#(type_def, arg))
        Error(_) -> None
      }
    }
    _ -> None
  }
}

/// Look up a constructor tag across all TypeDefs in the env.
///
/// Searches through the env for VTypeDef values, then looks up
/// the constructor by tag. Returns the @-bindings, self_type value,
/// and result_type term if found.
pub fn lookup_constructor(
  env: List(Value),
  tag: String,
) -> Option(#(List(String), Value, Term)) {
  // Direct VTypeDef lookup
  case list.find(env, fn(v) {
    case v {
      VTypeDef(_, _, constructors) ->
        list.any(constructors, fn(c) { c.0 == tag })
      _ -> False
    }
  }) {
    Ok(VTypeDef(_, params, constructors)) -> {
      case list.find(constructors, fn(c) { c.0 == tag }) {
        Ok(#(_tag, #(bindings, self_type_val, result_type_val), _)) -> {
          // The self_type and result_type values reference type params by name.
          // We need to evaluate them with the params as free variables.
          // For now, return the values as-is - they will be handled in infer_ctr.
          let _ = params
          Some(#(bindings, self_type_val, result_type_val))
        }
        Error(_) -> None
      }
    }
    _ -> None
  }
}

/// Unify a type pattern (self_type) against an argument type (arg_type).
///
/// Returns Option(List(#(Int, Value))) — Some(bindings) with the solved
/// unification variables (as De Bruijn levels -> values), None on failure.
///
/// The self_type pattern may contain VNeut(HVar(level), []) as unification
/// variables to solve for. Known values (from lambda-bound variables) are
/// treated as constants during unification.
///
/// ## Unification rules
///
/// - **HVar in pattern**: Bind it to the arg type (if not already bound)
/// - **VCtr**: Check same tag, recursively unify args
/// - **VRcdT**: Check same fields, recursively unify each field
/// - **Both are the same constructor literal**: Match
/// - **Otherwise**: Fail (structural mismatch)
pub fn unify_type_pattern(
  type_pattern: ast.Value,
  arg_type: ast.Value,
  acc: List(#(Int, ast.Value)),
) -> Option(List(#(Int, ast.Value))) {
  case type_pattern, arg_type {
    // Unification variable in pattern: bind it to the arg type
    ast.VNeut(ast.HVar(level), []), _ -> {
      // Check if already bound
      case list.find(acc, fn(b) { b.0 == level }) {
        Ok(#(_, existing_val)) -> {
          // Already bound: check consistency
          case unify_type_pattern(existing_val, arg_type, acc) {
            Some(_) -> Some(acc)
            None -> None
          }
        }
        Error(_) -> {
          // Bind the variable
          Some([#(level, arg_type), ..acc])
        }
      }
    }

    // HHole in pattern: treat as unification variable, bind to arg type
    ast.VNeut(ast.HHole(id), []), _ -> {
      // Check if already bound
      case list.find(acc, fn(b) { b.0 == id }) {
        Ok(#(_, existing_val)) -> {
          // Already bound: check consistency
          case unify_type_pattern(existing_val, arg_type, acc) {
            Some(_) -> Some(acc)
            None -> None
          }
        }
        Error(_) -> {
          // Bind the hole
          Some([#(id, arg_type), ..acc])
        }
      }
    }

    // arg_type is HHole: bind hole to the type_pattern
    _, ast.VNeut(ast.HHole(id), []) -> {
      case list.find(acc, fn(b) { b.0 == id }) {
        Ok(#(_, existing_val)) -> {
          case unify_type_pattern(existing_val, type_pattern, acc) {
            Some(_) -> Some(acc)
            None -> None
          }
        }
        Error(_) -> {
          Some([#(id, type_pattern), ..acc])
        }
      }
    }

    // arg_type is HVar: bind variable to the type_pattern
    _, ast.VNeut(ast.HVar(level), []) -> {
      case list.find(acc, fn(b) { b.0 == level }) {
        Ok(#(_, existing_val)) -> {
          case unify_type_pattern(existing_val, type_pattern, acc) {
            Some(_) -> Some(acc)
            None -> None
          }
        }
        Error(_) -> {
          Some([#(level, type_pattern), ..acc])
        }
      }
    }

    // Both are constructor types: check same tag, unify args
    ast.VCtr(tag1, arg1), ast.VCtr(tag2, arg2) ->
      case tag1 == tag2 {
        True -> unify_type_pattern(arg1, arg2, acc)
        False -> None
      }

    // Both are record types: check same fields, unify each
    ast.VRcdT(fields1), ast.VRcdT(fields2) ->
      unify_rcdt_fields(fields1, fields2, acc)

    // VRcd pattern vs VRcdT type: check that each field type matches
    ast.VRcd(fields1), ast.VRcdT(fields2) ->
      unify_rcd_vs_rcdt(fields1, fields2, acc)

    // Both are the same literal type: match
    ast.VLit(lit1), ast.VLit(lit2) ->
      case lit1 == lit2 {
        True -> Some(acc)
        False -> None
      }

    // Structural mismatch
    _, _ -> None
  }
}

/// Unify record type fields recursively.
fn unify_rcdt_fields(
  fields1: List(#(String, ast.Value, option.Option(ast.Value))),
  fields2: List(#(String, ast.Value, option.Option(ast.Value))),
  acc: List(#(Int, ast.Value)),
) -> Option(List(#(Int, ast.Value))) {
  case fields1 {
    [] -> Some(acc)
    [#(name1, type1, _default1), ..rest1] -> {
      case list.find(fields2, fn(f) { f.0 == name1 }) {
        Ok(#(_, type2, _)) -> {
          case unify_type_pattern(type1, type2, acc) {
            Some(new_acc) -> unify_rcdt_fields(rest1, fields2, new_acc)
            None -> None
          }
        }
        Error(_) -> None  // Field missing in arg type
      }
    }
  }
}

/// Unify a VRcd pattern against a VRcdT type.
/// Checks that each field value's type matches the corresponding field type.
fn unify_rcd_vs_rcdt(
  fields1: List(#(String, ast.Value)),
  fields2: List(#(String, ast.Value, option.Option(ast.Value))),
  acc: List(#(Int, ast.Value)),
) -> Option(List(#(Int, ast.Value))) {
  case fields1 {
    [] -> Some(acc)
    [#(name1, value1), ..rest1] -> {
      case list.find(fields2, fn(f) { f.0 == name1 }) {
        Ok(#(_, type2, _)) -> {
          let field_type = case value1 {
            ast.VLit(_) -> ast.VTyp(0)
            ast.VRcd(inner) -> ast.VRcdT(list.map(inner, fn(f) {
              #(f.0, ast.VTyp(0), None)
            }))
            ast.VRcdT(inner) -> ast.VRcdT(inner)
            ast.VCtr(_, _) -> ast.VTyp(0)
            ast.VCall(_, _, _) -> value1
            ast.VNeut(_, _) -> value1
            ast.VTypeDef(_, _, _) -> ast.VTyp(0)
            ast.VTyp(lvl) -> ast.VTyp(lvl + 1)
            ast.VLitT(_) -> ast.VTyp(0)
            ast.VErr -> ast.VErr
            ast.VLam(_, _, _, _) -> ast.VTyp(0)
            ast.VPi(_, _, _, _) -> ast.VTyp(0)
            ast.VFix(_, _, _) -> ast.VTyp(0)
          }
          case unify_type_pattern(field_type, type2, acc) {
            Some(new_acc) -> unify_rcd_vs_rcdt(rest1, fields2, new_acc)
            None -> None
          }
        }
        Error(_) -> None  // Field missing in arg type
      }
    }
  }
}

/// Apply unification bindings to a result type value.
///
/// Substitutes VNeut(HVar(level), spine) and VNeut(HHole(id), spine)
/// with the solved value from bindings (indexed by De Bruijn level).
/// This is essentially a lookup-based substitution for De Bruijn levels.
pub fn apply_unify_bindings(
  bindings: List(#(Int, ast.Value)),
  v: ast.Value,
) -> ast.Value {
  case v {
    ast.VNeut(ast.HVar(level, ), spine) -> {
      case list.find(bindings, fn(b) { b.0 == level }) {
        Ok(#(_, solved_val)) -> {
          // Apply the spine to the solved value
          apply_spine_to_value(solved_val, spine)
        }
        Error(_) -> v  // Not bound, leave as-is
      }
    }
    // HHole in result type: look up by De Bruijn level (same as HVar)
    ast.VNeut(ast.HHole(id), spine) -> {
      case list.find(bindings, fn(b) { b.0 == id }) {
        Ok(#(_, solved_val)) -> {
          apply_spine_to_value(solved_val, spine)
        }
        Error(_) -> ast.VNeut(ast.HHole(id), spine)  // Not bound, leave as-is
      }
    }
    // HFix: preserve the fixpoint neutral value as-is (not a bindable variable)
    ast.VNeut(ast.HFix(vfix), spine) -> ast.VNeut(ast.HFix(vfix), spine)
    ast.VLam(env, implicits, param, body) ->
      ast.VLam(env, implicits, param, body)
    ast.VPi(env, implicits, domain, codomain) ->
      ast.VPi(env, implicits, domain, codomain)
    ast.VLit(value) -> ast.VLit(value)
    ast.VCtr(tag, arg) -> ast.VCtr(tag, apply_unify_bindings(bindings, arg))
    ast.VRcd(fields) ->
      ast.VRcd(list.map(fields, fn(f) {
        #(f.0, apply_unify_bindings(bindings, f.1))
      }))
    ast.VRcdT(fields) ->
      ast.VRcdT(list.map(fields, fn(f) {
        let new_default = case f.2 {
          Some(d) -> Some(apply_unify_bindings(bindings, d))
          None -> None
        }
        #(f.0, apply_unify_bindings(bindings, f.1), new_default)
      }))
    ast.VCall(name, args, return_type) ->
      ast.VCall(
        name,
        list.map(args, fn(a) {
          #(apply_unify_bindings(bindings, a.0), apply_unify_bindings(bindings, a.1))
        }),
        apply_unify_bindings(bindings, return_type),
      )
    ast.VTypeDef(name, params, constructors) -> ast.VTypeDef(name, params, constructors)
    ast.VTyp(level) -> ast.VTyp(level)
    ast.VLitT(t) -> ast.VLitT(t)
    ast.VFix(name, env, body) -> ast.VFix(name, env, body)
    ast.VErr -> ast.VErr
  }
}

/// Apply unification bindings to a Term (for result_type substitution).
pub fn apply_unify_bindings_to_term(
  bindings: List(#(Int, ast.Value)),
  t: ast.Term,
) -> ast.Term {
  case t {
    ast.Var(level, span) -> {
      case list.find(bindings, fn(b) { b.0 == level }) {
        Ok(#(_, solved_val)) -> {
          // Convert solved value to a Var term (simple substitution)
          ast.Var(0, span)
        }
        Error(_) -> t  // Not bound, leave as-is
      }
    }
    ast.Hole(id, span) -> t
    ast.Lam(implicits, param, body, span) -> ast.Lam(implicits, param, apply_unify_bindings_to_term(bindings, body), span)
    ast.App(fun, arg, span) -> ast.App(apply_unify_bindings_to_term(bindings, fun), apply_unify_bindings_to_term(bindings, arg), span)
    ast.Pi(implicits, domain, codomain, span) -> ast.Pi(implicits, #(domain.0, apply_unify_bindings_to_term(bindings, domain.1)), apply_unify_bindings_to_term(bindings, codomain), span)
    ast.Lit(lit_value, span) -> t
    ast.Ctr(tag, arg, span) -> ast.Ctr(tag, apply_unify_bindings_to_term(bindings, arg), span)
    ast.Match(arg, cases, span) -> ast.Match(apply_unify_bindings_to_term(bindings, arg), list.map(cases, fn(c) {
      let new_guard = case c.guard {
        None -> None
        Some(g) -> Some(apply_unify_bindings_to_term(bindings, g))
      }
      ast.Case(c.pattern, new_guard, apply_unify_bindings_to_term(bindings, c.body), c.span)
    }), span)
    ast.Ann(term, type_, span) -> ast.Ann(apply_unify_bindings_to_term(bindings, term), apply_unify_bindings_to_term(bindings, type_), span)
    ast.Call(name, args, return_type, span) -> ast.Call(name, list.map(args, fn(a) { #(apply_unify_bindings_to_term(bindings, a.0), apply_unify_bindings_to_term(bindings, a.1)) }), apply_unify_bindings_to_term(bindings, return_type), span)
    ast.Rcd(fields, span) -> ast.Rcd(list.map(fields, fn(f) { #(f.0, apply_unify_bindings_to_term(bindings, f.1)) }), span)
    ast.RcdT(fields, span) -> ast.RcdT(list.map(fields, fn(f) {
      let new_default = case f.2 {
        None -> None
        Some(d) -> Some(apply_unify_bindings_to_term(bindings, d))
      }
      #(f.0, apply_unify_bindings_to_term(bindings, f.1), new_default)
    }), span)
    ast.Typ(universe, span) -> t
    ast.LitT(lit_type, span) -> t
    ast.TypeDef(name, params, constructors, span) -> ast.TypeDef(name, params, list.map(constructors, fn(c) {
      let #(tag, #(ctor_bindings, self_ty, return_type), span) = c
      #(tag, #(ctor_bindings, apply_unify_bindings_to_term(bindings, self_ty), apply_unify_bindings_to_term(bindings, return_type)), span)
    }), span)
    ast.Fix(name, body, span) -> ast.Fix(name, apply_unify_bindings_to_term(bindings, body), span)
    ast.Err(message, span) -> t
  }
}

/// Apply a spine to a value (for substitution).
fn apply_spine_to_value(v: ast.Value, spine: List(ast.Elim)) -> ast.Value {
  case spine {
    [] -> v
    [ast.EApp(_arg), ..rest] -> apply_spine_to_value(v, rest)
    [ast.EMatch(_env, _cases), ..rest] -> apply_spine_to_value(v, rest)
  }
}

/// Dummy do_match for force() calls in type-level operations.
/// Never called in practice since type-level values don't have EMatch eliminators.
fn dummy_do_match(
  _env: List(ast.Value),
  _truth_ctr: String,
  _ffi: List(state.FfiEntry),
  _scrutinee: ast.Value,
  _cases: List(ast.Case),
  _bindings: List(#(String, ast.Value)),
) -> ast.Value {
  ast.VErr
}

