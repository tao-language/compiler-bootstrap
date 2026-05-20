/// Type Inference — Bidirectional Type Checking
///
/// The `infer` module implements bidirectional type checking for the Core
/// language. Every term can be synthesized (inferred), and `check` is a
/// thin wrapper that synthesizes the term then unifies its type with
/// the expected type.
import core/ast
import core/eval.{eval}
import core/shift.{shift_value}
import core/state.{
  type FFI, type State, FfiEntry, State, env_to_state, state_to_env, with_err,
}
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
    // ast.Fix(name, body, span) -> infer_fix(state, name, body, span)
    // ast.App(fun, arg, span) -> infer_app(state, fun, arg, span)
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
  args: List(#(ast.Term, ast.Term)),
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
  args: List(#(ast.Term, ast.Term)),
) -> #(List(#(ast.Term, ast.Term)), State) {
  case args {
    [] -> #([], state)
    [#(arg, arg_type), ..args] -> {
      let #(arg, #(arg_type, _), state) = check_on_term(state, arg, arg_type)
      let #(args, state) = check_call_args(state, args)
      #([#(arg, arg_type), ..args], state)
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

fn infer_lam(
  state: State,
  implicits: List(#(String, ast.Term)),
  param_type: #(String, ast.Term),
  body: ast.Term,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let #(implicits, implicits_val, state) = push_param_list(state, implicits)
  let #(param_type, param_type_val, state) = push_param(state, param_type)
  let #(body, body_type, state) = infer(state, body)
  let #(env, state) = pop_params(state, list.length(implicits) + 1)
  #(
    ast.Lam(implicits, param_type, body, span),
    ast.VPi(env, implicits_val, param_type_val, body_type),
    state,
  )
}

fn push_param(
  state: State,
  param: #(String, ast.Term),
) -> #(#(String, ast.Term), #(String, ast.Value), State) {
  let #(name, param_type) = param
  let param_type_val = eval(state.ffi, state_to_env(state), param_type)
  let state = state.vars_shift(state, 1)
  let var = #(name, ast.vvar(0, []), param_type_val)
  #(
    #(name, param_type),
    #(name, param_type_val),
    State(..state, vars: [var, ..state.vars]),
  )
}

fn push_param_list(
  state: State,
  params: List(#(String, ast.Term)),
) -> #(List(#(String, ast.Term)), List(#(String, ast.Value)), State) {
  case params {
    [] -> #([], [], state)
    [param, ..params] -> {
      let #(param_type, param_type_val, state) = push_param(state, param)
      let #(params, params_val, state) = push_param_list(state, params)
      #([param_type, ..params], [param_type_val, ..params_val], state)
    }
  }
}

fn pop_params(state: State, num_params: Int) -> #(ast.Env, State) {
  let state = State(..state, vars: list.drop(state.vars, num_params))
  let env = state_to_env(state)
  let state = state.vars_shift(state, -num_params)
  #(env, state)
}

fn infer_pi(
  state: State,
  implicits: List(#(String, ast.Term)),
  domain: #(String, ast.Term),
  codomain: ast.Term,
  span: Span,
) -> #(ast.Term, ast.Value, State) {
  let #(implicits, _, state) = push_param_list(state, implicits)
  let #(domain, _, state) = push_param(state, domain)
  let #(codomain, _, state) = infer(state, codomain)
  let #(_, state) = pop_params(state, list.length(implicits) + 1)
  #(ast.Pi(implicits, domain, codomain, span), ast.VTyp(0), state)
}
