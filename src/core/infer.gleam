/// Type Inference — Bidirectional Type Checking
///
/// The `infer` module implements bidirectional type checking for the Core
/// language. Every term can be synthesized (inferred), and `check` is a
/// thin wrapper that synthesizes the term then unifies its type with
/// the expected type.
import core/ast
import core/eval.{eval}
import core/quote.{quote}
import core/shift.{shift_value}
import core/state.{
  type FFI, type State, State, env_to_state, state_to_env, with_err,
}
import core/subst
import core/unify.{unify}
import core/utils
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}

/// Infer the type of a term (synthesis).
///
/// Returns #(result_term, type_value, state) where:
/// - result_term is the original term with holes filled and implicit args expanded
/// - type_value is the inferred type (a Value)
/// - state is the updated state with any new bindings
pub fn infer(state: State, term: ast.Term) -> #(ast.Term, ast.Value, State) {
  case term {
    ast.Typ(level, span) -> infer_typ(state, level, span)
    ast.Hole(id, span) -> infer_hole(state, id, span)
    ast.Lit(value, span) -> infer_lit(state, value, span)
    ast.LitT(t, span) -> infer_litt(state, t, span)
    ast.Var(index, span) -> infer_var(state, index, span)
    ast.Ctr(tag, arg, span) -> infer_ctr(state, tag, arg, span)
    ast.Rcd(fields, span) -> infer_rcd(state, fields, span)
    ast.RcdT(fields, span) -> infer_rcd_type(state, fields, span)
    ast.Call(name, args, return_type, span) ->
      infer_call(state, name, args, return_type, span)
    ast.Ann(inner, type_, _) -> infer_ann(state, inner, type_)
    ast.Lam(implicits, param, body, span) ->
      infer_lam(state, implicits, param, body, span)
    ast.Pi(implicits, domain, codomain, span) ->
      infer_pi(state, implicits, domain, codomain, span)
    ast.Fix(name, body, span) -> infer_fix(state, name, body, span)
    ast.App(fun, arg, span) -> infer_app(state, fun, arg, span)
    // ast.TypeDef(params, constructors, span) ->
    //   infer_type_def(state, params, constructors, span)
    // ast.Match(arg, cases, span) -> infer_match(state, arg, cases, span)
    // ast.Err(message, span) -> infer_err(state, message, span)
    _ -> todo
  }
}

/// Check that a term has the expected type (verification).
///
/// This is a thin wrapper: infer the term, then fill in any missing
/// record defaults at the value level before unifying.
pub fn check(
  state: State,
  term: ast.Term,
  expected: #(ast.Value, Span),
) -> #(ast.Term, ast.Value, State) {
  let #(term, type_, state) = infer(state, term)
  let state = unify(state, #(type_, ast.get_span(term)), expected)
  let type_ = subst.force_value(state.ffi, state.subst, type_)
  #(term, type_, state)
}

fn check_on_term(
  state: State,
  term: ast.Term,
  type_: ast.Term,
) -> #(ast.Term, #(ast.Term, ast.Value), State) {
  let env = state_to_env(state)
  let #(type_, _, state) = infer(state, type_)
  let type_val = eval(state.ffi, env, type_)
  let #(term, type_val, state) =
    check(state, term, #(type_val, ast.get_span(type_)))
  #(term, #(type_, type_val), state)
}

/// Infer a type universe ($Type<n>).
/// $Type<n> evaluates to VTyp(n), with type VTyp(n+1).
fn infer_typ(
  state: State,
  level: Int,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  #(ast.Typ(level, span), ast.VTyp(level + 1), state)
}

fn infer_hole(
  state: State,
  id: Int,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  case id >= 0 {
    True -> {
      // Concrete hole, create a new hole for its type.
      let #(type_id, state) = state.new_hole(state)
      #(ast.Hole(id, span), ast.VNeut(ast.HHole(type_id), []), state)
    }
    False -> {
      // Unknown hole, instantiate a fresh new hole.
      let #(id, state) = state.new_hole(state)
      infer_hole(state, id, span)
    }
  }
}

fn infer_lit(
  state: State,
  value: ast.Literal,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let type_ = case value {
    ast.Int(_) -> ast.VLitT(ast.IntT)
    ast.Float(_) -> ast.VLitT(ast.FloatT)
  }
  #(ast.Lit(value, span), type_, state)
}

/// Infer a literal type annotation ($Int, $Float, $I32, etc.).
/// The value is the literal type itself (e.g., $Int), and its type is $Type<0>.
fn infer_litt(
  state: State,
  value: ast.LiteralType,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  #(ast.LitT(value, span), ast.VTyp(0), state)
}

fn infer_var(
  state: State,
  index: Int,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  case utils.list_at(state.vars, index) {
    Some(#(_name, _value, type_)) -> #(ast.Var(index, span), type_, state)
    None -> {
      let state = with_err(state, state.VarUndefined(index, span))
      #(ast.Var(index, span), ast.VErr, state)
    }
  }
}

fn infer_ctr(
  state: State,
  tag: String,
  arg: ast.Term,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let #(arg, arg_type, state) = infer(state, arg)
  #(ast.Ctr(tag, arg, span), ast.VCtr(tag, arg_type), state)
}

fn infer_rcd(
  state: State,
  fields: List(#(String, ast.Term)),
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let #(fields, field_types, state) = infer_rcd_fields(state, fields)
  #(ast.Rcd(fields, span), ast.VRcdT(field_types), state)
}

fn infer_rcd_fields(
  state: State,
  fields: List(#(String, ast.Term)),
) -> #(
  List(#(String, ast.Term)),
  List(#(String, ast.Value, Option(ast.Value))),
  State,
) {
  case fields {
    [] -> #([], [], state)
    [#(name, term), ..fields] -> {
      let #(term, type_, state) = infer(state, term)
      let #(fields, field_types, state) = infer_rcd_fields(state, fields)
      #([#(name, term), ..fields], [#(name, type_, None), ..field_types], state)
    }
  }
}

fn infer_rcd_type(
  state: State,
  fields: List(#(String, ast.Term, option.Option(ast.Term))),
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let #(fields, state) = infer_rcd_type_fields(state, fields)
  #(ast.RcdT(fields, span), ast.VTyp(0), state)
}

fn infer_rcd_type_fields(
  state: State,
  fields: List(#(String, ast.Term, option.Option(ast.Term))),
) -> #(List(#(String, ast.Term, option.Option(ast.Term))), State) {
  case fields {
    [] -> #([], state)
    [#(name, type_, default), ..fields] -> {
      let #(field, state) = case default {
        Some(term) -> {
          let #(term, #(type_, _), state) = check_on_term(state, term, type_)
          let field = #(name, type_, Some(term))
          #(field, state)
        }
        None -> {
          let #(type_, _, state) = infer(state, type_)
          let field = #(name, type_, None)
          #(field, state)
        }
      }
      let #(fields, state) = infer_rcd_type_fields(state, fields)
      #([field, ..fields], state)
    }
  }
}

fn infer_call(
  state: State,
  name: String,
  args: List(ast.Term),
  return_type: ast.Term,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let #(args, state) = check_call_args(state, args)
  let #(return_type, _, state) = infer(state, return_type)
  let env = state_to_env(state)
  let return_type_val = eval(state.ffi, env, return_type)
  #(ast.Call(name, args, return_type, span), return_type_val, state)
}

fn check_call_args(
  state: State,
  args: List(ast.Term),
) -> #(List(ast.Term), State) {
  case args {
    [] -> #([], state)
    [arg, ..args] -> {
      let #(arg, _, state) = infer(state, arg)
      let #(args, state) = check_call_args(state, args)
      #([arg, ..args], state)
    }
  }
}

fn infer_ann(
  state: State,
  term: ast.Term,
  type_: ast.Term,
) -> #(ast.Term, ast.Value, State) {
  let #(term, #(_, type_val), state) = check_on_term(state, term, type_)
  #(term, type_val, state)
}

/// Infer a lambda term: $fn<implicits>(param: param_type) => body
///
/// DeBruijn management strategy (critical for soundness in dependent types):
///
/// 1. push_param_list / push_param: prepend each param to state.vars, and
///    shift ALL existing vars' values by +1 so their DeBruijn levels stay
///    correct relative to the new innermost binder.
/// 2. infer(body): body type is inferred with params in scope; its DeBruijn
///    levels are relative to the lambda's parameter block.
/// 3. build_implicit_env: extract implicit params from state.vars and build
///    the implicit environment with holes. Each implicit's value is a hole
///    (VNeut(HHole(n), [])) so unify can bind it to concrete types during
///    application. This is how implicit parameters get "resolved".
/// 4. pop_params: drop the lambda's own params from the front of vars, then
///    extract the captured environment from the remaining vars.
///    — The implicits are extracted BEFORE the -delta shift, so they retain
///      the +delta offset from push_param. This is the key invariant:
///      implicit values are already correct for the VPi's binding context.
///    — The -delta shift on the state restores original levels for the outer
///      scope, but does NOT affect the implicits (which are already returned).
///
/// The body_type (codomain of VPi) needs no shifting: its levels were already
/// computed inside the lambda's scope where params are at indices 0..n.
fn infer_lam(
  state: State,
  implicits: List(#(String, ast.Term)),
  param: #(String, ast.Term),
  body: ast.Term,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let #(implicits, _, state) = push_param_list(state, implicits)
  let #(param, param_type_val, state) = push_param(state, param)
  let #(body, body_type_val, state) = infer(state, body)
  // Build implicit values from the implicit params' values (as holes for unify)
  let implicit_values = build_implicit_values(state, list.length(implicits))
  // Domain is #(name, param_type_val)
  let domain_val = #(param.0, param_type_val)
  let #(_, _, state) = pop_params(state, list.length(implicits) + 1)
  #(
    ast.Lam(implicits, param, body, span),
    ast.VPi(implicit_values, domain_val, body_type_val),
    state,
  )
}

fn push_param(
  state: State,
  param: #(String, ast.Term),
) -> #(#(String, ast.Term), ast.Value, State) {
  let #(name, param_type) = param
  // Evaluate the param type in the current env (may reference earlier implicits)
  let param_type_val = eval(state.ffi, state_to_env(state), param_type)
  let state = push_param_val(state, #(name, param_type_val))
  #(#(name, param_type), param_type_val, state)
}

fn push_param_val(state: State, param: #(String, ast.Value)) -> State {
  let #(name, param_type_val) = param
  // Shift ALL existing vars' values by +1 BEFORE prepending. This is critical:
  // every var's value and type must be shifted so its DeBruijn levels remain
  // correct relative to the new innermost binder (the param we're adding).
  // Without this shift, existing vars' levels would be off by 1.
  let state = state.vars_shift(state, 1)
  // Also shift param_type_val by +1 so the new param's type references
  // the correct variables in the shifted environment.
  //
  // Why: param_type_val was evaluated in the pre-shift environment, where
  // binder X was at level N. After the shift, X moves to level N+1. If we
  // don't shift param_type_val, it still points to level N, which now
  // refers to a DIFFERENT binder (the one that was at N-1 before the shift).
  //
  // Example: pushing x with type a, in env [b, a] (a at level 1):
  //   - param_type_val = vvar(1, [])  (evaluated: a is at level 1)
  //   - After shift: env = [b', a'] where b' is at level 1, a' at level 2
  //   - Without shifting param_type_val: x's type = vvar(1, []) = b'  ✗
  //   - With shifting: x's type = vvar(2, []) = a'  ✓
  let var = #(name, ast.vvar(0, []), shift_value(param_type_val, 1))
  State(..state, vars: [var, ..state.vars])
}

fn push_param_list(
  state: State,
  params: List(#(String, ast.Term)),
) -> #(List(#(String, ast.Term)), List(ast.Value), State) {
  case params {
    [] -> #([], [], state)
    [param, ..params] -> {
      let #(param, param_type_val, state) = push_param(state, param)
      let #(params, param_type_vals, state) = push_param_list(state, params)
      #([param, ..params], [param_type_val, ..param_type_vals], state)
    }
  }
}

/// Build the implicit values from the implicit params in state.vars.
///
/// Each implicit parameter's value is represented as a hole (VNeut(HHole(n), []))
/// so that during application, unify can bind the hole to the argument's type.
/// This is the mechanism by which implicit parameters get "resolved".
///
/// The implicit params are at the END of state.vars (outermost in DeBruijn order),
/// after the explicit param. We drop the explicit param (1 element) and take
/// the implicit params, then reverse to get innermost-first order.
///
/// The returned list is in innermost-first order.
fn build_implicit_values(
  state: State,
  num_implicits: Int,
) -> List(#(String, ast.Value)) {
  // Drop the explicit param (1 element at front), take implicit params,
  // and reverse to get innermost-first order
  list.drop(state.vars, 1)
  |> list.take(num_implicits)
  |> list.reverse
  |> list.index_map(fn(var, i) {
    let #(name, _, _) = var
    #(name, ast.vhole(i, []))
  })
}

/// Remove the lambda's own params from the state and extract the captured env.
///
/// Key invariant: env is extracted BEFORE the -delta shift, so env values
/// retain the +delta offset from push_param. This means env levels are
/// already correct for the VPi's binding context (where lambda params occupy
/// levels 0..n, and captured vars occupy levels n+1, n+2, ...).
///
/// The -delta shift on the state then restores the remaining vars to their
/// original levels (relative to the outer scope), but the env is unaffected.
///
/// Returns: #(param_type_value, env, state)
fn pop_params(
  state: State,
  num_params: Int,
) -> #(ast.Value, ast.Env, State) {
  // Extract the explicit param's type value before dropping params.
  // state.vars[0] = #(name, var_value, type_value)
  let param_type_val =
    case state.vars {
      [#(_name, _var_val, type_val), .._] -> type_val
      _ -> ast.VErr
    }
  // Drop the lambda's params (which are at the front of vars)
  let state = State(..state, vars: list.drop(state.vars, num_params))
  // Extract captured env from remaining vars — these values have +num_params
  // levels from push_param, which are exactly the levels needed for the VPi.
  let env = state_to_env(state)
  // Restore the remaining vars to their original levels for the outer scope.
  let state = state.vars_shift(state, -num_params)
  #(param_type_val, env, state)
}

/// Infer a Pi type: $pi<implicits>(domain: param_type) -> codomain
///
/// Uses the same DeBruijn management strategy as infer_lam:
///   1. push_param_list / push_param: shift existing vars' values by +1
///   2. infer(codomain): codomain inferred with params in scope
///   3. build_implicit_values: extract implicit params with holes for unify
///   4. pop_params: drop params, shift state back
///
/// Pi types are types, so their type is $Type (VTyp(0)).
fn infer_pi(
  state: State,
  implicits: List(#(String, ast.Term)),
  domain: #(String, ast.Term),
  codomain: ast.Term,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let #(implicits, _, state) = push_param_list(state, implicits)
  let #(domain, domain_val, state) = push_param(state, domain)
  let #(_, codomain_val, state) = infer(state, codomain)
  let implicit_values = build_implicit_values(state, list.length(implicits))
  let #(_, _, state) = pop_params(state, list.length(implicits) + 1)
  #(
    ast.Pi(implicits, domain, codomain, span),
    ast.VTyp(0),
    state,
  )
}

fn infer_fix(
  state: State,
  name: String,
  body: ast.Term,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let #(hole_id, state) = state.new_hole(state)
  let type_hole = ast.vhole(hole_id, [])
  let state = push_param_val(state, #(name, type_hole))
  let #(body, body_type, state) = infer(state, body)
  let #(_, _, state) = pop_params(state, 1)
  let state = unify(state, #(type_hole, span), #(body_type, span))
  #(ast.Fix(name, body, span), body_type, state)
}

fn infer_app(
  state: State,
  fun: ast.Term,
  arg: ast.Term,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let #(fun, fun_type, state) = infer(state, fun)
  case fun_type {
    ast.VPi(implicit_values, domain, codomain) -> {
      // 1. Infer the argument's type first (may contain holes to be resolved)
      let #(arg, arg_type, state) = infer(state, arg)

      // 2. Unify arg_type with domain's type value (already a Value)
      //    This resolves implicit parameters:
      //    - If domain is a hole (implicit param), it gets bound to arg_type
      //    - If domain is concrete, arg_type must match
      let state = unify(state, #(arg_type, ast.get_span(arg)), #(domain.1, span))

      // 3. Force substitutions to resolve any holes
      let arg_type = subst.force_value(state.ffi, state.subst, arg_type)
      let resolved_implicit_values =
        list.map(implicit_values, fn(v) {
          subst.force_value(state.ffi, state.subst, v.1)
        })

      // 4. Build evaluation environment:
      //    - Arg value at index 0
      //    - Resolved implicit values at indices 1..n
      let eval_env = list.append([arg_type], resolved_implicit_values)

      // 5. Evaluate the codomain in the constructed environment
      //    to resolve any De Bruijn level references
      let codomain_val = eval.eval_value(state.ffi, eval_env, codomain)

      #(ast.App(fun, arg, span), codomain_val, state)
    }
    _ -> {
      let #(_, _, state) = infer(state, arg)
      let state = with_err(state, state.NotAFunction(fun_type, span))
      #(ast.Err(span), ast.VErr, state)
    }
  }
}
