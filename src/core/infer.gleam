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
  type State, FfiEntry, State, env_to_state, state_to_env, with_err,
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
    // ast.Pi(implicits, domain, codomain, span) ->
    //   infer_pi(state, implicits, domain, codomain, span)
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
  let num_params = list.length(implicits) + 1
  let state = pop_params(state, num_params)
  let env = list.map(state_to_env(state), shift_value(_, num_params))
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
  let new_var = #(name, ast.vvar(0, []), param_type_val)
  let state = State(..state, vars: [new_var, ..state.vars])
  #(#(name, param_type), #(name, param_type_val), state)
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

fn pop_params(state: State, num_params: Int) -> State {
  State(..state, vars: list.drop(state.vars, num_params))
}
//

// fn infer_pi(
//   state: State,
//   _implicits: List(#(String, ast.Term)),
//   domain: #(String, ast.Term),
//   codomain: ast.Term,
//   span: Span,
// ) -> #(ast.Term, ast.Value, State) {
//   let dom_name = domain.0
//   let dom_term = domain.1
//   let dom_val = evaluate(state_to_env(state), state.ffi, dom_term)
//   let codom_val = evaluate(state_to_env(state), state.ffi, codomain)
//   let pi_type = ast.VPi([], [], #(dom_name, dom_val), codom_val)
//   // Pi types are types, so their type is * (VTyp(0))
//   let filled_codomain = fill_holes_in_term(state, codomain)
//   let filled_domain = #(dom_name, fill_holes_in_term(state, dom_term))
//   #(ast.Pi([], filled_domain, filled_codomain, span), ast.VTyp(0), state)
// }

// fn infer_fix(
//   state: State,
//   name: String,
//   body: ast.Term,
//   span: Span,
// ) -> #(ast.Term, ast.Value, State) {
//   // Bind `f` with a fresh hole so references to `f` within the body
//   // can be resolved during inference. The hole acts as a placeholder
//   // that inference will solve into a Pi type.
//   let fresh_id = state.hole_counter
//   let hole_ref = ast.VNeut(ast.HHole(fresh_id), [])
//   let bound_value = ast.VNeut(ast.HVar(0), [])
//   let state_bound =
//     State(..state, hole_counter: fresh_id + 1, vars: [
//       #(name, #(bound_value, hole_ref)),
//       ..state.vars
//     ])

//   // Infer the body with `f` bound in the environment.
//   let #(body_result, body_type, state2) = infer(state_bound, body)
//   let _ = body_result

//   // Shift body by -1 so `f` (Var(2) after term_to_debruijn due to pattern
//   // variable shadowing) becomes Var(1) relative to the VLam's parameter.
//   let shifted_body = ast.shift_term_from(body_result, -1, 1)

//   let fix_value = ast.VFix(name, [bound_value], shifted_body)

//   let fix_type = ast.VPi([], [], #(name, body_type), body_type)

//   #(ast.Fix(name, body_result, span), fix_type, state2)
// }

// fn infer_app(
//   state: State,
//   fun: ast.Term,
//   arg: ast.Term,
//   span: Span,
// ) -> #(ast.Term, ast.Value, State) {
//   // Check if this is a $let binding: App(Lam(name, _, body), value, span)
//   // If so, infer the arg, fill defaults at value level, add to env, infer body.
//   case fun {
//     ast.Lam(implicits, #(param_name, param_type), body, _lam_span) -> {
//       // This is a let binding: App(Lam("x", param_type, body), arg)
//       // Infer the argument to get its result term and type
//       let #(arg_result, arg_type, state2) = infer(state, arg)
//       // Evaluate the parameter type to get the expected value type
//       let param_val = evaluate(state_to_env(state2), state2.ffi, param_type)
//       // Fill in record defaults at the term level
//       let filled_arg = fill_record_defaults_term(arg_result, param_val)
//       // Int→Float conversion if param type is FloatT
//       let converted_arg = case param_val {
//         ast.VLitT(ast.FloatT) ->
//           case filled_arg {
//             ast.Lit(ast.Int(v), s) ->
//               case float.parse(int.to_string(v) <> ".0") {
//                 Ok(f) -> ast.Lit(ast.Float(f), s)
//                 Error(_) -> filled_arg
//               }
//             _ -> filled_arg
//           }
//         _ -> filled_arg
//       }
//       // Update the lambda's env to include itself for recursive self-reference.
//       let updated_lam = case term_to_value(converted_arg) {
//         ast.VLam(env, implicits, param, body) ->
//           ast.VLam(
//             list.append(env, [term_to_value(converted_arg)]),
//             implicits,
//             param,
//             body,
//           )
//         _ ->
//           ast.VLam(
//             [],
//             [],
//             #("_", ast.VNeut(ast.HHole(0), [])),
//             ast.Hole(0, single("", 0, 0)),
//           )
//       }
//       // If the lambda has implicit params, add them to the state before the lambda param
//       // State order must be: [implicit_holes..., let_bound_var]
//       // so that body indices match: Var(0)..Var(n-1) = implicits, Var(n) = lambda param
//       let n = list.length(implicits)
//       let #(updated_lam, state_ext) = case implicits {
//         [] -> #(updated_lam, def_var(state2, param_name, updated_lam, arg_type))
//         [_, ..] -> {
//           // Let binding case with implicit params:
//           // Add implicit params FIRST (so they're at indices 0..n-1),
//           // then add the let-bound variable (at index n).
//           // The implicit param's VALUE is the argument's type (e.g., VLitT(IntT)),
//           // and its TYPE is the implicit param's declared type (e.g., VTyp(0)).
//           let state_with_implicits =
//             list.fold(
//               list.reverse(implicits),
//               def_var(state2, param_name, updated_lam, arg_type),
//               fn(s, imp) {
//                 let ival = evaluate(state_to_env(s), s.ffi, imp.1)
//                 // Use arg_type as the implicit param's VALUE
//                 def_var(s, imp.0, arg_type, ival)
//               },
//             )
//           #(updated_lam, state_with_implicits)
//         }
//       }
//       // Infer the body directly — its indices are relative to the extended state
//       let #(body_result, body_type, state_final) = infer(state_ext, body)
//       #(body_result, body_type, state_final)
//     }
//     _ -> {
//       // Normal function application: infer both fun and arg
//       let #(fun_result, fun_type, state2) = infer(state, fun)
//       let #(arg_result, arg_type, state3) = infer(state2, arg)
//       let fun_val = term_to_value(fun_result)

//       // Try to normalize via beta reduction
//       case fun_val {
//         // β-reduction: apply VLam to argument
//         ast.VLam(lam_env, implicits, #(_pname, param_type), body) -> {
//           // Fill defaults if param_type is VRcdT
//           let filled_arg = fill_record_defaults_term(arg_result, param_type)
//           // Int→Float conversion if param type is FloatT
//           let converted_arg = case param_type {
//             ast.VLitT(ast.FloatT) ->
//               case filled_arg {
//                 ast.Lit(ast.Int(v), s) ->
//                   case float.parse(int.to_string(v) <> ".0") {
//                     Ok(f) -> ast.Lit(ast.Float(f), s)
//                     Error(_) -> filled_arg
//                   }
//                 _ -> filled_arg
//               }
//             _ -> filled_arg
//           }
//           // The lambda body's De Bruijn indices are already correct:
//           // indices 0..n-1 = implicit params, index n = lambda param, index n+1+ = outer scope
//           // We do NOT shift the body.

//           // Handle implicit params: create fresh holes, bind them, extend state
//           let #(body_final, state_final) = case implicits {
//             [] -> {
//               // No implicit params: simple beta reduction
//               // Extend env with converted_arg (lambda param value)
//               let env_with_param =
//                 list.append(lam_env, [term_to_value(converted_arg)])
//               let body_state = env_to_state(env_with_param, state3.ffi)
//               #(body, body_state)
//             }
//             [_, ..] -> {
//               // Has implicit params: bind them to the argument's type.
//               // When Var(0) is looked up in the body, it should find the
//               // argument's type (e.g., VLitT(IntT)), not a fresh hole.
//               //
//               // State order must be:
//               //   Var(0)..Var(n-1) = implicit params (arg_type in state)
//               //   Var(n) = lambda param (converted_arg)
//               //
//               // Since def_var prepends to the list, we add the lambda param
//               // FIRST, then add implicit params in reverse order.
//               let state_with_lam =
//                 def_var(
//                   state3,
//                   "_param",
//                   term_to_value(converted_arg),
//                   param_type,
//                 )
//               let state_with_implicits =
//                 list.fold(list.reverse(implicits), state_with_lam, fn(s, imp) {
//                   // imp.1 is the implicit param's type Value (e.g., VTyp(0))
//                   // Use arg_type as the implicit param's VALUE (e.g., VLitT(IntT))
//                   let ival = imp.1
//                   def_var(s, imp.0, arg_type, ival)
//                 })
//               #(body, state_with_implicits)
//             }
//           }
//           infer(state_final, body_final)
//         }
//         // VFix unroll: substitute arg for Var(0), VFix for Var(1)
//         ast.VFix(fix_name, fix_env, fix_body) -> {
//           let body = case fix_body {
//             ast.Ann(inner, _, _) -> inner
//             _ -> fix_body
//           }
//           case body {
//             ast.Lam(_implicits, _param, body_term, _) -> {
//               let arg_val = term_to_value(arg_result)
//               let body_with_arg = subst_term_var(0, arg_val, body_term)
//               let self = ast.VFix(fix_name, fix_env, fix_body)
//               let body_with_self = subst_term_var(1, self, body_with_arg)
//               let env_with_arg = list.append([arg_val], fix_env)
//               let body_state = env_to_state(env_with_arg, state3.ffi)
//               infer(body_state, body_with_self)
//             }
//             _ -> #(ast.Err("VFix unroll failed", span), ast.VErr, state3)
//           }
//         }
//         // Neutral spine: extend with argument
//         ast.VNeut(head, spine) -> {
//           let arg_val = term_to_value(arg_result)
//           let _new_neut =
//             ast.VNeut(head, list.append(spine, [ast.EApp(arg_val)]))
//           #(fun_result, fun_type, state3)
//         }
//         // Error propagates
//         ast.VErr -> #(ast.Err("Application error", span), ast.VErr, state3)
//         // Cannot apply a type/value that isn't a function
//         _ -> {
//           let new_state =
//             state.with_err(state, state.NotAFunction(fun_type, span))
//           #(ast.Err("Not a function", span), ast.VErr, new_state)
//         }
//       }
//     }
//   }
// }

// fn infer_match(
//   state: State,
//   arg: ast.Term,
//   cases: List(ast.Case),
//   span: Span,
// ) -> #(ast.Term, ast.Value, State) {
//   let #(arg_result, arg_type, state2) = infer(state, arg)
//   let #(result_term, result_type, final_state) =
//     check_match_cases(state2, arg_result, arg_type, cases, [])

//   // Check exhaustiveness if the scrutinee type is a TypeDef
//   let final_state = case arg_type {
//     VTypeDef(name: _, params: _, constructors: constructors) -> {
//       let covered_tags = collect_covered_tags(cases, arg_result)
//       check_exhaustiveness_vdef(final_state, constructors, covered_tags, span)
//     }
//     _ -> final_state
//   }

//   // result_term is the checked body of the matching case
//   // Return the Match term with the result body
//   #(ast.Match(arg_result, cases, span), result_type, final_state)
// }

// fn infer_type_def(
//   state: State,
//   params: List(#(String, ast.Term)),
//   constructors: List(#(String, #(List(String), ast.Term, ast.Term), Span)),
//   span: Span,
// ) -> #(ast.Term, ast.Value, State) {
//   // Infer type params and bind them as fresh holes.
//   // This ensures that type parameter references in self_type and result_type
//   // resolve to the *same* hole for the same parameter name, enabling proper
//   // unification during GADT constructor checking.
//   //
//   // For example, in `Option<a> { #Some(a) -> #Option(a) }`, the `a` in both
//   // self_type and result_type must be the same unification variable.
//   let #(hole_bindings, new_state) =
//     list.fold(params, #([], state), fn(acc, p) {
//       let #(acc_bindings, s) = acc
//       let fresh_id = s.hole_counter
//       let new_state = State(..s, hole_counter: fresh_id + 1)
//       let _param_val = evaluate(state_to_env(new_state), new_state.ffi, p.1)
//       let hole = ast.VNeut(ast.HHole(fresh_id), [])
//       let updated_state = def_var(new_state, p.0, hole, hole)
//       #([#(p.0, hole), ..acc_bindings], updated_state)
//     })

// fn check_match_cases(
//   state: State,
//   scrutinee_result: ast.Term,
//   scrutinee_type: ast.Value,
//   cases: List(ast.Case),
//   acc: List(#(ast.Value, ast.Value)),
// ) -> #(ast.Term, ast.Value, State) {
//   // Convert scrutinee result term to value for pattern matching
//   let scrutinee_val = case scrutinee_result {
//     ast.Lit(lit, _) -> ast.VLit(lit)
//     ast.Var(_, _) -> ast.VNeut(ast.HVar(0), [])
//     ast.Hole(_, _) -> ast.VNeut(ast.HHole(0), [])
//     ast.Err(_, _) -> ast.VErr
//     _ -> ast.VNeut(ast.HHole(0), [])
//   }
//   case cases {
//     [] -> #(ast.Err("No matching case", single("", 0, 0)), ast.VErr, state)
//     [ast.Case(pattern, _guard, body, _span), ..rest] -> {
//       case match_pattern(pattern, scrutinee_val, []) {
//         Ok(bindings) -> {
//           // Pattern matched: check the body and return immediately
//           let body_state =
//             State(
//               ..state,
//               vars: list.map(bindings, fn(b) {
//                 #(b.0, #(b.1, ast.VNeut(ast.HHole(0), [])))
//               }),
//             )
//           check(body_state, body, scrutinee_type)
//         }
//         Error(_) -> {
//           // Pattern didn't match: try next case
//           check_match_cases(state, scrutinee_result, scrutinee_type, rest, acc)
//         }
//       }
//     }
//   }
// }

// fn infer_err(
//   state: State,
//   message: String,
//   span: Span,
// ) -> #(ast.Term, ast.Value, State) {
//   #(ast.Err(message, span), ast.VErr, state)
// }
