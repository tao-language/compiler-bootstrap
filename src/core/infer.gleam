// ============================================================================
// CORE INFER - Type Inference
// ============================================================================
import gleam/list
import gleam/int
import gleam/string
import gleam/option.{type Option, None, Some}
import syntax/grammar.{type Span, Span}
import core/ast as ast
import core/state as state
import core/eval.{do_app, eval}
import core/quote as quote
import core/subst as subst
import core/unify as unify
import core/generalize as generalize
import core/exhaustiveness as exhaustiveness

// ============================================================================
// ANNOTATION FRESHENING
// ============================================================================
/// Replace negative hole IDs in annotation types with fresh positive IDs.
///
/// This prevents the InfiniteType bug where multiple annotation types share
/// the same negative hole ID (e.g., Hole(-1)), and after evaluation they
/// all become the same HHole(-1), causing unification cycles.
///
/// Each call to freshen_annotation starts with a fresh counter (typically 0),
/// ensuring isolation between different annotations.
pub fn freshen_annotation(term: ast.Term, counter: Int) -> #(ast.Term, Int) {
  case term {
    ast.Hole(id, span) -> {
      case id < 0 {
        True -> #(ast.Hole(counter, span), counter + 1)
        False -> #(term, counter)  // Preserve non-negative holes
      }
    }
    ast.Pi(implicit, name, domain, codomain, span) -> {
      let #(fresh_dom, c1) = freshen_annotation(domain, counter)
      let #(fresh_cod, c2) = freshen_annotation(codomain, c1)
      #(ast.Pi(implicit, name, fresh_dom, fresh_cod, span), c2)
    }
    ast.Lam(implicit, param, body, span) -> {
      let #(name, param_ty) = param
      let #(fresh_param_ty, c1) = freshen_annotation(param_ty, counter)
      let #(fresh_body, c2) = freshen_annotation(body, c1)
      #(ast.Lam(implicit, #(name, fresh_param_ty), fresh_body, span), c2)
    }
    ast.Ctr(tag, arg, span) -> {
      let #(fresh_arg, c1) = freshen_annotation(arg, counter)
      #(ast.Ctr(tag, fresh_arg, span), c1)
    }
    ast.App(fun, implicit, arg, span) -> {
      let #(fresh_fun, c1) = freshen_annotation(fun, counter)
      let #(fresh_arg, c2) = freshen_annotation(arg, c1)
      #(ast.App(fresh_fun, implicit, fresh_arg, span), c2)
    }
    ast.Rcd(fields, span) -> {
      let #(fresh_fields, c1) = freshen_fields(fields, counter)
      #(ast.Rcd(fresh_fields, span), c1)
    }
    ast.Match(arg, motive, cases, span) -> {
      let #(fresh_arg, c1) = freshen_annotation(arg, counter)
      let #(fresh_motive, c2) = freshen_annotation(motive, c1)
      #(ast.Match(fresh_arg, fresh_motive, cases, span), c2)
    }
    ast.Dot(arg, field, span) -> {
      let #(fresh_arg, c1) = freshen_annotation(arg, counter)
      #(ast.Dot(fresh_arg, field, span), c1)
    }
    ast.Ann(inner, typ, span) -> {
      let #(fresh_inner, c1) = freshen_annotation(inner, counter)
      let #(fresh_typ, c2) = freshen_annotation(typ, c1)
      #(ast.Ann(fresh_inner, fresh_typ, span), c2)
    }
    ast.Call(name, args, span) -> {
      let #(fresh_args, c1) = freshen_term_list(args, counter)
      #(ast.Call(name, fresh_args, span), c1)
    }
    ast.Fix(name, body, span) -> {
      let #(fresh_body, c1) = freshen_annotation(body, counter)
      #(ast.Fix(name, fresh_body, span), c1)
    }
    ast.Comptime(inner, span) -> {
      let #(fresh_inner, c1) = freshen_annotation(inner, counter)
      #(ast.Comptime(fresh_inner, span), c1)
    }
    ast.Let(name, value, body, span) -> {
      let #(fresh_value, c1) = freshen_annotation(value, counter)
      let #(fresh_body, c2) = freshen_annotation(body, c1)
      #(ast.Let(name, fresh_value, fresh_body, span), c2)
    }
    // Terms without sub-terms that can contain holes
    ast.Typ(_, _) | ast.Lit(_, _) | ast.LitT(_, _) | ast.Var(_, _) | ast.Unit(_) | ast.Err(_, _) ->
      #(term, counter)
  }
}

fn freshen_fields(
  fields: List(#(String, ast.Term)),
  counter: Int,
) -> #(List(#(String, ast.Term)), Int) {
  case fields {
    [] -> #([], counter)
    [#(name, field), ..rest] -> {
      let #(fresh_field, c1) = freshen_annotation(field, counter)
      let #(fresh_rest, c2) = freshen_fields(rest, c1)
      #([#(name, fresh_field), ..fresh_rest], c2)
    }
  }
}

fn freshen_term_list(terms: List(ast.Term), counter: Int) -> #(List(ast.Term), Int) {
  case terms {
    [] -> #([], counter)
    [term, ..rest] -> {
      let #(fresh_term, c1) = freshen_annotation(term, counter)
      let #(fresh_rest, c2) = freshen_term_list(rest, c1)
      #([fresh_term, ..fresh_rest], c2)
    }
  }
}

pub fn infer(s: state.State, term: ast.Term) -> #(ast.Value, ast.Type, state.State) {
  case term {
    ast.Typ(k, span) -> #(ast.VTyp(k), ast.VTyp(k + 1), s)
    ast.Lit(k, span) -> #(ast.VLit(k), typeof_lit(k), s)
    ast.LitT(k, span) -> #(ast.VLitT(k), ast.VTyp(0), s)
    ast.Var(i, span) ->
      case ctx_get(s.vars, i) {
        Some(#(val, ty)) -> {
          let forced_ty = subst.force(s.ffi, s.subst, ty)
          #(val, forced_ty, s)
        }
        None -> {
          let s = state.State(..s, errors: [state.VarUndefined(i, span), ..s.errors])
          #(ast.VErr, ast.VErr, s)
        }
      }
    ast.Hole(id, span) -> {
      // Negative holes (from desugarer) are "unknown types" that need instantiation.
      // Instantiate each one into a fresh positive hole, ensuring uniqueness.
      case id < 0 {
        True -> {
          // Desugarer hole: instantiate into a fresh positive hole
          let #(hole_ty, new_s) = new_hole(s)
          // Value and type are both the fresh hole
          #(hole_ty, hole_ty, new_s)
        }
        False -> {
          // Positive hole: create it, mark as unsolved
          let hole_id = s.hole_counter
          let hole_ty = ast.VNeut(ast.HHole(hole_id), [])
          let new_s = state.State(..s, hole_counter: s.hole_counter + 1, errors: [state.HoleUnsolved(hole_id, span), ..s.errors])
          #(ast.VNeut(ast.HHole(hole_id), []), hole_ty, new_s)
        }
      }
    }
    ast.Rcd(fields, span) -> {
      let #(fields_val, fields_ty, s) = infer_fields(s, fields)
      #(ast.VRcd(fields_val), ast.VRcd(fields_ty), s)
    }
    ast.Ctr(tag, arg, span) ->
      case list.key_find(s.ctrs, tag) {
        Error(Nil) -> {
          let s = state.State(..s, errors: [state.CtrUndefined(tag, span), ..s.errors])
          #(ast.VErr, ast.VErr, s)
        }
        Ok(ctr) -> {
          let #(params, ctr_arg_ty, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          let #(_, arg_ty, s) = infer(s, arg)
          let #(s, _) = check_type(s, arg_ty, ctr_arg_ty, get_span(arg), get_span(ctr.arg_ty))
          let #(param_vals, s) = subst.ctr_solve_params(s, ctr, params, tag, span)
          let env = list.append(param_vals, get_env(s))
          let arg_val = eval.eval(s.ffi, env, arg)
          let ret_ty_val = eval.eval(s.ffi, env, ctr.ret_ty)
          #(ast.VCtrValue(ast.VCtr(tag, arg_val)), ret_ty_val, s)
        }
      }
    ast.Unit(span) -> #(ast.VUnit, ast.VTyp(0), s)
    ast.Dot(arg, name, span) -> {
      let #(arg_val, arg_ty, s) = infer(s, arg)
      case arg_ty {
        ast.VRcd(fields) ->
          case list.key_find(fields, name) {
            Ok(ty) -> {
              let val = ast.VNeut(ast.HVar(0), [ast.EDot(name)])
              #(val, ty, s)
            }
            Error(Nil) -> {
              let s = state.State(..s, errors: [state.DotFieldNotFound(name, fields, span), ..s.errors])
              #(ast.VErr, ast.VErr, s)
            }
          }
        ast.VErr -> #(ast.VErr, ast.VErr, s)
        _ -> {
          let s = state.State(..s, errors: [state.DotOnNonCtr(arg_ty, name, span), ..s.errors])
          #(ast.VErr, ast.VErr, s)
        }
      }
    }
    ast.Ann(inner, ann_ty, span) -> {
      let ty_val = eval.eval(s.ffi, get_env(s), ann_ty)
      let #(val, s) = check(s, inner, ty_val, span)
      #(val, ty_val, s)
    }
    ast.Lam(implicit, param, body, span) -> {
      let #(name, param_ty_term) = param
      let env = get_env(s)
      let holes_before = s.hole_counter

      // Create implicit param placeholders (holes) for each implicit name
      let #(implicit_hole_ids, s) = create_implicit_holes(implicit, s)
      let implicit_bindings = create_implicit_bindings_from_holes(implicit, implicit_hole_ids)
      let s = state.State(..s, vars: list.append(implicit_bindings, s.vars))

      let #(domain_val, s) = case param_ty_term {
        ast.Hole(_, _) -> new_hole(s)
        _ -> {
          // KEY FIX: Freshen negative holes in the param type before evaluation.
          // This ensures each lambda's param type gets unique hole IDs.
          let #(fresh_ty, _counter) = freshen_annotation(param_ty_term, 0)
          #(eval.eval(s.ffi, get_env(s), fresh_ty), s)
        }
      }
      // Bind variable at current level, then increment for the body
      let #(_fresh, s) = def_var(s, name, domain_val)
      let s = state.State(..s, level: s.level + 1)

      // Increment lambda depth before inferring body (track nesting)
      let s = state.State(..s, lambda_depth: s.lambda_depth + 1)
      let #(body_val, body_ty, s) = infer(s, body)
      // Decrement lambda depth after inferring the body
      let s = state.State(..s, lambda_depth: s.lambda_depth - 1)

      // Decrement level after inferring the body
      let s = state.State(..s, level: s.level - 1)

      // KEY FIX: For polymorphic lambdas, the codomain should refer to the domain,
      // not be a separate generalized hole. When body_ty equals domain_val (e.g., x -> x),
      // we should use the domain as the codomain after generalization.
      let domain_forced = subst.force(s.ffi, s.subst, domain_val)
      let codomain_forced = subst.force(s.ffi, s.subst, body_ty)
      let domain_holes = subst.free_holes_in_value(domain_forced)
      let codomain_holes = subst.free_holes_in_value(codomain_forced)
      let all_holes = list.unique(list.append(domain_holes, codomain_holes))

      // Filter holes: only generalize holes at current lambda depth
      // Holes from nested lambdas (deeper depth) should NOT be generalized here
      let current_depth = s.lambda_depth
      let holes_to_generalize =
        list.filter(all_holes, fn(id) {
          case list.key_find(s.hole_depths, id) {
            Ok(hole_depth) -> hole_depth == current_depth
            Error(Nil) -> True  // If no depth recorded, include it (shouldn't happen)
          }
        })

      // Always generalize for lambdas to ensure polymorphic types
      let quote_lvl = list.length(env) + list.length(implicit) + 1
      let #(final_implicit, final_t1, final_t2_term) = generalize_holes_wrapper(
        holes_to_generalize,
        implicit,
        domain_val,
        body_ty,
        s,
        s.ffi,
        quote_lvl,
        span,
      )

      let num_new_implicit = list.length(final_implicit) - list.length(implicit)
      let quote_lvl = list.length(env) + list.length(implicit) + num_new_implicit + 1
      let body_quoted = quote.quote(s.ffi, quote_lvl, body_val, get_span(body))
      // Use the generalized codomain term (shifted for the outer context)
      let final_t2_shifted = shift_hvar_in_term(final_t2_term, num_new_implicit)

      // Build VPi environment: implicit param HVars + domain value
      // The domain value must be included so codomain can reference it via Var(0)
      // With absolute HVar levels, the domain is at level (s.level - 1) after decrementing
      let implicit_hvars = case final_implicit {
        [] -> []
        [_] -> [ast.VNeut(ast.HVar(0), [])]
        [_, _] -> [ast.VNeut(ast.HVar(0), []), ast.VNeut(ast.HVar(1), [])]
        _ -> list.index_map(final_implicit, fn(_, idx) { ast.VNeut(ast.HVar(idx), []) })
      }
      // Domain value is at the current level (after decrementing, this is the lambda's binder level)
      let domain_level = s.level - 1
      let domain_hvar = ast.VNeut(ast.HVar(domain_level), [])
      let vpi_env = list.append(implicit_hvars, [domain_hvar])

      #(
        ast.VLam(final_implicit, name, env, body_quoted),
        ast.VPi(final_implicit, name, vpi_env, final_t1, final_t2_shifted),
        s,
      )
    }
    ast.Pi(implicit, name, in_term, out_term, span) -> {
      let env = get_env(s)
      let #(in_val, _, s) = infer(s, in_term)
      let #(_, s) = def_var(s, name, in_val)
      // Increment level for the codomain - it's in the scope of the bound variable
      let s = state.State(..s, level: s.level + 1)
      let #(_, _, s) = infer(s, out_term)
      let s = state.State(..s, level: s.level - 1)
      #(ast.VPi(implicit, name, env, in_val, out_term), ast.VTyp(0), s)
    }
    ast.App(fun, implicit, arg, span) -> infer_app(s, fun, implicit, arg, span)
    ast.Match(arg, motive, cases, span) -> infer_match(s, arg, motive, cases, span)
    ast.Call(name, args, span) -> infer_call(s, name, args, span)
    ast.Comptime(inner, span) -> {
      let val = eval.eval(s.ffi, [], inner)
      let quoted = quote.quote(s.ffi, 0, val, span)
      infer(s, quoted)
    }
    ast.Fix(name, body, span) -> infer_fix(s, name, body, span)
    ast.Let(name, value, body, span) -> {
      // For recursive bindings (e.g., Let(name, Fix(name, ...), body)),
      // the value needs to see `name` in the environment.
      // Bind name to a hole first, then infer the value, then update with the actual type.
      //
      // KEY: def_var prepends to position 0 of s.vars (De Bruijn position, not name lookup).
      // After infer(value), inner bindings from check(Lam) are prepended, pushing the
      // Let-bound name down. We must restore the saved vars state (where position 0 IS
      // the Let-bound name) and update only position 0's type.
      let #(hole_ty, s) = new_hole(s)
      let #(_fresh, s) = def_var(s, name, hole_ty)
      // Save: position 0 is the Let-bound name (def_var always prepends)
      let saved_vars = s.vars
      let s1 = state.State(..s, level: s.level + 1)
      let #(val_val, val_ty, s2) = infer(s1, value)
      // Restore saved vars state, updating position 0's type to the inferred value type
      let restored_vars = case saved_vars {
        [#(n, #(val, _old_ty)), ..rest] -> [#(n, #(val, val_ty)), ..rest]
        [] -> []
      }
      let s2 = state.State(..s2, vars: restored_vars)
      let #(body_val, body_ty, s3) = infer(s2, body)
      let s4 = state.State(..s3, level: s3.level - 1)
      #(body_val, body_ty, s4)
    }
    ast.Err(_, span) -> #(ast.VErr, ast.VErr, s)
  }
}

fn typeof_lit(literal: ast.Literal) -> ast.Type {
  case literal {
    ast.I32(_) -> ast.VLitT(ast.I32T)
    ast.I64(_) -> ast.VLitT(ast.I64T)
    ast.U32(_) -> ast.VLitT(ast.U32T)
    ast.U64(_) -> ast.VLitT(ast.U64T)
    ast.F32(_) -> ast.VLitT(ast.F32T)
    ast.F64(_) -> ast.VLitT(ast.F64T)
  }
}

fn infer_app(
  s: state.State,
  fun: ast.Term,
  implicit: List(ast.Term),
  arg: ast.Term,
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  let #(fun_val, fun_ty, s) = infer(s, fun)
  let fun_ty_forced = subst.force(s.ffi, s.subst, fun_ty)
  case fun_ty_forced {
    ast.VPi(implicit_params, _, pi_env, domain, codomain) -> {
      // Instantiate implicit type variables with fresh holes
      let #(implicit_subst, s) = subst.instantiate_implicit_params(implicit_params, s)

      // KEY FIX: If the domain is a hole and there are implicit params,
      // add the domain hole to the implicit subst for the first implicit param.
      // This ensures the codomain term references the domain hole directly.
      let implicit_subst = case implicit_params, domain {
        [_, ..], ast.VNeut(ast.HHole(domain_hole_id), []) -> {
          // Check if the first implicit param's instantiation is a hole
          case implicit_subst {
            [#(0, ast.VNeut(ast.HHole(implicit_hole_id), [])), ..rest] -> {
              // Replace the first implicit param's instantiation with the domain hole
              [#(0, ast.VNeut(ast.HHole(domain_hole_id), [])), ..rest]
            }
            _ -> implicit_subst
          }
        }
        _, _ -> implicit_subst
      }

      // Apply substitution to domain and codomain
      let domain_instantiated =
        subst.subst_value_with_implicit_vars(implicit_subst, domain)
      let codomain_instantiated =
        subst.subst_term_with_implicit_vars(implicit_subst, codomain)

      // Check argument against instantiated domain
      let #(arg_val, s) = check(s, arg, domain_instantiated, get_span(arg))
      // Instantiate implicit params in pi_env before evaluating codomain
      // This ensures HVar placeholders are replaced with fresh holes
      let pi_env_instantiated = list.map(pi_env, fn(v) { 
        subst.subst_value_with_implicit_vars(implicit_subst, v) 
      })
      // Evaluate codomain with instantiated environment
      let out_val = eval(s.ffi, [arg_val, ..pi_env_instantiated], codomain_instantiated)
      let out_val_forced = subst.force(s.ffi, s.subst, out_val)
      #(do_app(s.ffi, get_env(s), fun, implicit, arg, span), out_val_forced, s)
    }
    ast.VNeut(ast.HHole(hole_id), spine) -> {
      // Hole expansion: ?1 applied to arg means ?1 = (?2 -> ?3)
      // KEY FIX: Use empty environment for the expanded VPi.
      // The codomain is a simple Hole term that doesn't reference any variables,
      // so capturing the current environment (which contains HVar values from
      // enclosing lambdas) can create cycles when those HVar types contain holes
      // that get unified with the original hole.
      
      // KEY FIX 2: Infer the argument's type FIRST, then check for cycles
      // before expanding the hole. This prevents creating a cycle where
      // the domain hole gets unified with the original hole.
      let #(arg_val, arg_ty, s1) = infer(s, arg)
      
      // Check if the argument's type contains the original hole.
      // If so, expanding the hole would create a cycle:
      //   hole_id = (arg_ty -> ?)
      //   arg_ty contains hole_id
      // Therefore: hole_id = (hole_id -> ...) - infinite type!
      case unify.occurs(s1.subst, hole_id, arg_ty) {
        True -> {
          // Would create infinite type - return InfiniteType error
          #(ast.VErr, ast.VErr, state.with_err(s1, state.InfiniteType(hole_id, arg_ty, get_span(arg), span)))
        }
        False -> {
          // Safe to expand
          let result_ty_hole_id = s1.hole_counter
          let #(result_ty_hole_val, s2) = new_hole(s1)
          
          // KEY FIX: Check if the argument's type is already solved to something
          // containing the original hole. This can happen if the argument's type
          // was unified with something else before this application.
          let arg_ty_forced = subst.force(s2.ffi, s2.subst, arg_ty)
          case unify.occurs(s2.subst, hole_id, arg_ty_forced) {
            True -> {
              // Argument's solved type contains the original hole - would create cycle
              #(ast.VErr, ast.VErr, state.with_err(s2, state.InfiniteType(hole_id, arg_ty_forced, get_span(arg), span)))
            }
            False -> {
              // Create the expanded function type: (arg_ty -> ?3)
              // KEY FIX: Use the argument's type DIRECTLY as the domain, not a new hole.
              // This prevents the domain hole from being unified with something containing
              // the original hole, which would create a cycle.
              let fun_ty_expanded =
                ast.VPi(
                  [],
                  "_",
                  [],  // Empty environment - codomain doesn't reference any variables
                  arg_ty,  // Use argument's type directly as domain
                  ast.Hole(result_ty_hole_id, span),
                )
              // Unify the original hole with the expanded type
              case unify.unify_result(s2, ast.VNeut(ast.HHole(hole_id), []), fun_ty_expanded, span, span) {
                Ok(s3) -> {
                  // Force the result hole through substitution to get the solved type
                  let out_val = subst.force(s3.ffi, s3.subst, result_ty_hole_val)
                  #(do_app(s3.ffi, get_env(s3), fun, implicit, arg, span), out_val, s3)
                }
                Error(_) -> {
                  case fun_ty {
                    ast.VErr -> #(ast.VErr, ast.VErr, s2)
                    _ -> #(ast.VErr, ast.VErr, state.with_err(s2, state.NotAFunction(fun, fun_ty)))
                  }
                }
              }
            }
          }
        }
      }
    }
    ast.VNeut(ast.HStepLimit, _) -> {
      // Step limit exceeded - return error
      #(ast.VErr, ast.VErr, state.with_err(s, state.NotAFunction(fun, fun_ty)))
    }
    _ -> {
      // Avoid adding duplicate error if fun_ty is already VErr
      case fun_ty {
        ast.VErr -> #(ast.VErr, ast.VErr, s)
        _ -> #(ast.VErr, ast.VErr, state.with_err(s, state.NotAFunction(fun, fun_ty)))
      }
    }
  }
}

pub fn infer_match(
  s: state.State,
  arg: ast.Term,
  motive: ast.Term,
  cases: List(ast.Case),
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  // Step 1: Infer argument to get scrutinee type
  let #(arg_val, arg_ty, s) = infer(s, arg)

  // Step 2: Infer motive FIRST to get the expected result type
  let #(motive_val, motive_ty, s) = infer(s, motive)

  // Step 3: Extract motive result type (codomain for dependent, or a fresh hole)
  let #(motive_result_ty, s) = extract_motive_result_type(s, motive_val, motive_ty)

  // Step 4: Check each case body against the motive result type
  let #(case_results, s) = check_cases(s, cases, arg_ty, motive_result_ty)

  // Step 5: Exhaustiveness checking
  let patterns = list.map(cases, fn(c) { [c.pattern] })
  let exhaustiveness_errors = exhaustiveness.check_exhaustiveness(patterns, [arg_ty], span)
  let s = list.fold(exhaustiveness_errors, s, fn(s, err) {
    state.with_err(s, err)
  })

  // Step 6: Build result value
  let result_val = ast.VNeut(ast.HVar(0), [ast.EMatch([], motive_val, case_results)])
  // Return the result type (motive_result_ty), not the motive type
  #(result_val, motive_result_ty, s)
}

/// Extract the result type from a motive.
/// For dependent motives (λp. ResultTy), extract ResultTy.
/// For non-dependent motives, return the type as-is.
fn extract_motive_result_type(s: state.State, motive_val: ast.Value, motive_ty: ast.Type) -> #(ast.Type, state.State) {
  case motive_val {
    ast.VLam(_, _, env, body_term) -> {
      // Motive is a lambda - evaluate body to get result type.
      // Any negative holes in body_term were already instantiated to fresh
      // positive holes during infer, so no special handling needed.
      let body_val = eval.eval(s.ffi, env, body_term)
      #(body_val, s)
    }
    ast.VPi(_, _, env, _domain, codomain) -> {
      // Motive type is a Pi type - extract codomain as result type
      let codomain_val = eval.eval(s.ffi, env, codomain)
      #(codomain_val, s)
    }
    _ -> #(motive_ty, s)
  }
}

/// Check all case bodies against the expected result type.
fn check_cases(
  s: state.State,
  cases: List(ast.Case),
  arg_ty: ast.Type,
  result_ty: ast.Type,
) -> #(List(ast.Case), state.State) {
  check_cases_loop(s, cases, arg_ty, result_ty, [])
}

fn check_cases_loop(
  s: state.State,
  cases: List(ast.Case),
  arg_ty: ast.Type,
  result_ty: ast.Type,
  acc: List(ast.Case),
) -> #(List(ast.Case), state.State) {
  case cases {
    [] -> #(list.reverse(acc), s)
    [c, ..rest] -> {
      let patterns = [c.pattern]
      let body = c.body
      // Infer patterns to bind pattern variables
      let #(pattern_vals, s) = infer_patterns(s, patterns, arg_ty)
      // Check body against result type
      let #(body_val, s) = check(s, body, result_ty, get_span(body))
      // Update case with checked body
      let checked_case = ast.Case(c.pattern, body, c.guard, c.span)
      check_cases_loop(s, rest, arg_ty, result_ty, [checked_case, ..acc])
    }
  }
}

fn infer_patterns(
  s: state.State,
  patterns: List(ast.Pattern),
  arg_ty: ast.Type,
) -> #(List(ast.Value), state.State) {
  infer_patterns_loop(s, patterns, arg_ty, [])
}

fn infer_patterns_loop(
  s: state.State,
  patterns: List(ast.Pattern),
  arg_ty: ast.Type,
  acc: List(ast.Value),
) -> #(List(ast.Value), state.State) {
  case patterns {
    [] -> #(list.reverse(acc), s)
    [pattern, ..rest] -> {
      let #(pattern_val, s) = infer_pattern(s, pattern, arg_ty)
      infer_patterns_loop(s, rest, arg_ty, [pattern_val, ..acc])
    }
  }
}

fn infer_pattern(
  s: state.State,
  pattern: ast.Pattern,
  expected_ty: ast.Type,
) -> #(ast.Value, state.State) {
  case pattern {
    ast.PAs(inner_pattern, name) -> {
      let hole_val = ast.VNeut(ast.HHole(0), [])
      let #(_fresh, s) = def_var(s, name, expected_ty)
      infer_pattern(s, inner_pattern, expected_ty)
    }
    ast.PCtr(tag, arg_pattern) -> {
      case list.key_find(s.ctrs, tag) {
        Ok(ctr) -> {
          let #(params, ctr_arg_ty, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          let #(s, _) = check_type(s, expected_ty, ctr_ret_ty, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
          let #(arg_val, s) = infer_pattern(s, arg_pattern, ctr_arg_ty)
          #(ast.VCtrValue(ast.VCtr(tag, arg_val)), s)
        }
        Error(Nil) -> {
          let s = state.State(..s, errors: [state.CtrUndefined(tag, Span("", 0, 0, 0, 0)), ..s.errors])
          #(ast.VErr, s)
        }
      }
    }
    ast.PLit(literal) -> {
      let val = case literal {
        ast.I32(n) -> ast.VLit(ast.I32(n))
        ast.I64(n) -> ast.VLit(ast.I64(n))
        ast.U32(n) -> ast.VLit(ast.U32(n))
        ast.U64(n) -> ast.VLit(ast.U64(n))
        ast.F32(f) -> ast.VLit(ast.F32(f))
        ast.F64(f) -> ast.VLit(ast.F64(f))
      }
      #(val, s)
    }
    ast.PLitT(lit_type) -> #(ast.VLitT(lit_type), s)
    ast.PTyp(k) -> #(ast.VTyp(k), s)
    ast.PRcd(fields) -> {
      let #(field_vals, s) = infer_pattern_fields(s, fields)
      #(ast.VRcd(field_vals), s)
    }
    ast.PUnit -> #(ast.VUnit, s)
    ast.PAny -> #(ast.VNeut(ast.HHole(0), []), s)
  }
}

fn infer_pattern_fields(
  s: state.State,
  fields: List(#(String, ast.Pattern)),
) -> #(List(#(String, ast.Value)), state.State) {
  infer_pattern_fields_loop(s, fields, [])
}

fn infer_pattern_fields_loop(
  s: state.State,
  fields: List(#(String, ast.Pattern)),
  acc: List(#(String, ast.Value)),
) -> #(List(#(String, ast.Value)), state.State) {
  case fields {
    [] -> #(list.reverse(acc), s)
    [#(name, pattern), ..rest] -> {
      let #(val, s) = infer_pattern(s, pattern, ast.VErr)
      infer_pattern_fields_loop(s, rest, [#(name, val), ..acc])
    }
  }
}

fn infer_call(
  s: state.State,
  name: String,
  args: List(ast.Term),
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  case list.key_find(s.ffi, name) {
    Ok(state.Builtin(impl, _)) -> {
      let #(arg_vals, arg_tys, s) = infer_args(s, args)
      case impl(arg_vals) {
        Some(result_val) -> {
          let result_ty = case arg_tys {
            [ty, ..] -> ty
            [] -> ast.VErr
          }
          #(result_val, result_ty, s)
        }
        None -> {
          let result_ty = case arg_tys {
            [ty, ..] -> ty
            [] -> ast.VErr
          }
          #(ast.VCall(name, arg_vals), result_ty, s)
        }
      }
    }
    Error(Nil) -> {
      let #(arg_vals, arg_tys, s) = infer_args(s, args)
      let result_ty = case arg_tys {
        [ty, ..] -> ty
        [] -> ast.VErr
      }
      #(ast.VCall(name, arg_vals), result_ty, s)
    }
  }
}

fn infer_fix(
  s: state.State,
  name: String,
  body: ast.Term,
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  let env = get_env(s)
  case body {
    ast.Ann(lam, ann_ty, _ann_span) -> {
      // KEY FIX: Freshen negative hole IDs in the annotation type before evaluation.
      // This prevents multiple annotation types from sharing the same HHole(-1)
      // after evaluation, which causes unification cycles (InfiniteType errors).
      let #(fresh_ann_ty, _counter) = freshen_annotation(ann_ty, 0)
      let ann_ty_val = eval.eval(s.ffi, env, fresh_ann_ty)
      // NOTE: Do NOT call def_var here. The sequential Lam wrapper (from
      // build_sequential_loop in the desugaring layer) already binds `name`
      // to the same type. Calling def_var here would add a DUPLICATE entry,
      // shifting all De Bruijn indices in the Fix body and causing type
      // mismatches for modules with 3+ functions.
      // Increment level for the body - it's in the scope of the fix-bound name
      let s = state.State(..s, level: s.level + 1)
      let #(body_val, s) = check(s, lam, ann_ty_val, span)
      let s = state.State(..s, level: s.level - 1)
      // If body is VErr, return VErr type instead of annotation type
      let result_ty = case body_val {
        ast.VErr -> ast.VErr
        _ -> ann_ty_val
      }
      #(ast.VFix(name, env, body), result_ty, s)
    }
    _ -> {
      let #(result_ty_hole, s) = new_hole(s)
      // NOTE: Do NOT call def_var here. The sequential Lam wrapper already
      // binds `name` (to a hole as well, since there's no annotation).
      // Increment level for the body - it's in the scope of the fix-bound name
      let s = state.State(..s, level: s.level + 1)
      let #(body_val, s) = check(s, body, result_ty_hole, span)
      let s = state.State(..s, level: s.level - 1)
      // If body is VErr, return VErr type instead of solved hole
      let solved_ty = case body_val {
        ast.VErr -> ast.VErr
        _ -> subst.force(s.ffi, s.subst, result_ty_hole)
      }
      #(ast.VFix(name, env, body), solved_ty, s)
    }
  }
}

fn infer_args(s: state.State, args: List(ast.Term)) -> #(List(ast.Value), List(ast.Type), state.State) {
  infer_args_loop(s, args, [], [])
}

fn infer_args_loop(
  s: state.State,
  args: List(ast.Term),
  vals_acc: List(ast.Value),
  tys_acc: List(ast.Type),
) -> #(List(ast.Value), List(ast.Type), state.State) {
  case args {
    [] -> #(list.reverse(vals_acc), list.reverse(tys_acc), s)
    [arg, ..rest] -> {
      let #(val, ty, s) = infer(s, arg)
      infer_args_loop(s, rest, [val, ..vals_acc], [ty, ..tys_acc])
    }
  }
}

fn infer_fields(
  s: state.State,
  fields: List(#(String, ast.Term)),
) -> #(List(#(String, ast.Value)), List(#(String, ast.Type)), state.State) {
  infer_fields_loop(s, fields, [], [])
}

fn infer_fields_loop(
  s: state.State,
  fields: List(#(String, ast.Term)),
  vals_acc: List(#(String, ast.Value)),
  tys_acc: List(#(String, ast.Type)),
) -> #(List(#(String, ast.Value)), List(#(String, ast.Type)), state.State) {
  case fields {
    [] -> #(list.reverse(vals_acc), list.reverse(tys_acc), s)
    [#(name, term), ..rest] -> {
      let #(val, ty, s) = infer(s, term)
      infer_fields_loop(s, rest, [#(name, val), ..vals_acc], [#(name, ty), ..tys_acc])
    }
  }
}

fn ctx_get(ctx: List(#(String, #(ast.Value, ast.Type))), index: Int) -> Option(#(ast.Value, ast.Type)) {
  ctx_get_loop(ctx, index, 0)
}

fn ctx_get_loop(
  ctx: List(#(String, #(ast.Value, ast.Type))),
  index: Int,
  current: Int,
) -> Option(#(ast.Value, ast.Type)) {
  case ctx {
    [] -> None
    [#(_, val_ty), ..rest] -> {
      case current == index {
        True -> Some(val_ty)
        False -> ctx_get_loop(rest, index, current + 1)
      }
    }
  }
}

fn get_env(s: state.State) -> ast.Env {
  list.map(s.vars, fn(pair) { pair.1.0 })
}

fn def_var(s: state.State, name: String, ty: ast.Value) -> #(ast.Value, state.State) {
  // Use absolute level for HVar index (De Bruijn level from root)
  let var_val = ast.VNeut(ast.HVar(s.level), [])
  let s = state.State(..s, vars: [#(name, #(var_val, ty)), ..s.vars])
  #(var_val, s)
}

/// Update the type of the most recently added variable binding.
/// Used for recursive Let bindings where the value's type is inferred after
/// the name is bound to a hole.
fn update_last_var_type(
  vars: List(#(String, #(ast.Value, ast.Type))),
  new_ty: ast.Type,
) -> List(#(String, #(ast.Value, ast.Type))) {
  case vars {
    [] -> []
    [#(name, #(val, _old_ty)), ..rest] -> [#(name, #(val, new_ty)), ..rest]
  }
}

fn new_hole(s: state.State) -> #(ast.Type, state.State) {
  let id = s.hole_counter
  let hole_ty = ast.VNeut(ast.HHole(id), [])
  // Record the hole depth for proper generalization filtering
  let s = state.State(
    ..s,
    hole_counter: id + 1,
    hole_depths: [#(id, s.lambda_depth), ..s.hole_depths],
  )
  #(hole_ty, s)
}

fn create_implicit_holes(implicit: List(String), s: state.State) -> #(List(Int), state.State) {
  create_implicit_holes_loop(implicit, s, [])
}

fn create_implicit_holes_loop(
  implicit: List(String),
  s: state.State,
  acc: List(Int),
) -> #(List(Int), state.State) {
  case implicit {
    [] -> #(list.reverse(acc), s)
    [_name, ..rest] -> {
      let id = s.hole_counter
      let s = state.State(..s, hole_counter: id + 1)
      create_implicit_holes_loop(rest, s, [id, ..acc])
    }
  }
}

fn create_implicit_bindings_from_holes(implicit: List(String), hole_ids: List(Int)) -> List(#(String, #(ast.Value, ast.Type))) {
  create_implicit_bindings_loop(implicit, hole_ids, [])
}

fn create_implicit_bindings_loop(
  implicit: List(String),
  hole_ids: List(Int),
  acc: List(#(String, #(ast.Value, ast.Type))),
) -> List(#(String, #(ast.Value, ast.Type))) {
  case implicit, hole_ids {
    [], _ -> list.reverse(acc)
    _, [] -> list.reverse(acc)
    [name, ..names], [id, ..ids] -> {
      let hole_val = ast.VNeut(ast.HHole(id), [])
      let binding = #(name, #(hole_val, hole_val))
      create_implicit_bindings_loop(names, ids, [binding, ..acc])
    }
  }
}

fn generalize_holes_wrapper(
  holes: List(Int),
  implicit: List(String),
  domain: ast.Value,
  codomain: ast.Type,
  s: state.State,
  ffi: state.FFI,
  lvl: Int,
  span: Span,
) -> #(List(String), ast.Value, ast.Term) {
  generalize.generalize_holes(holes, implicit, domain, codomain, s, ffi, lvl, span)
}




fn shift_hvar_in_term(term: ast.Term, shift: Int) -> ast.Term {
  case term {
    ast.Var(index, span) if index >= shift -> ast.Var(index + shift, span)
    ast.Var(_, _) -> term
    ast.Lam(implicit, param, body, span) -> {
      ast.Lam(implicit, param, shift_hvar_in_term(body, shift), span)
    }
    ast.Pi(implicit, name, in_term, out_term, span) -> {
      ast.Pi(implicit, name, shift_hvar_in_term(in_term, shift), shift_hvar_in_term(out_term, shift + 1), span)
    }
    ast.App(fun, implicit, arg, span) -> {
      ast.App(shift_hvar_in_term(fun, shift), implicit, shift_hvar_in_term(arg, shift), span)
    }
    ast.Ann(inner, ty, span) -> {
      ast.Ann(shift_hvar_in_term(inner, shift), shift_hvar_in_term(ty, shift), span)
    }
    ast.Hole(_, _) -> term
    ast.Typ(_, _) -> term
    ast.Lit(_, _) -> term
    ast.LitT(_, _) -> term
    ast.Unit(_) -> term
    ast.Rcd(fields, span) -> {
      ast.Rcd(list.map(fields, fn(pair) { #(pair.0, shift_hvar_in_term(pair.1, shift)) }), span)
    }
    ast.Ctr(tag, arg, span) -> {
      ast.Ctr(tag, shift_hvar_in_term(arg, shift), span)
    }
    ast.Dot(arg, name, span) -> {
      ast.Dot(shift_hvar_in_term(arg, shift), name, span)
    }
    ast.Match(arg, motive, cases, span) -> {
      ast.Match(
        shift_hvar_in_term(arg, shift),
        shift_hvar_in_term(motive, shift),
        list.map(cases, fn(c) {
          let shifted_pattern = shift_hvar_in_pattern(c.pattern, shift)
          let shifted_body = shift_hvar_in_term(c.body, shift + 1)
          ast.Case(pattern: shifted_pattern, body: shifted_body, guard: c.guard, span: c.span)
        }),
        span,
      )
    }
    ast.Call(name, args, span) -> {
      ast.Call(name, list.map(args, fn(a) { shift_hvar_in_term(a, shift) }), span)
    }
    ast.Comptime(inner, span) -> {
      ast.Comptime(shift_hvar_in_term(inner, shift), span)
    }
    ast.Fix(name, body, span) -> {
      ast.Fix(name, shift_hvar_in_term(body, shift + 1), span)
    }
    ast.Let(name, value, body, span) -> {
      ast.Let(name, shift_hvar_in_term(value, shift), shift_hvar_in_term(body, shift + 1), span)
    }
    ast.Err(_, _) -> term
  }
}

fn shift_hvar_in_pattern(pattern: ast.Pattern, shift: Int) -> ast.Pattern {
  case pattern {
    ast.PAs(inner, name) -> ast.PAs(shift_hvar_in_pattern(inner, shift), name)
    ast.PCtr(tag, arg) -> ast.PCtr(tag, shift_hvar_in_pattern(arg, shift))
    ast.PLit(_) -> pattern
    ast.PLitT(_) -> pattern
    ast.PTyp(_) -> pattern
    ast.PRcd(fields) -> ast.PRcd(list.map(fields, fn(pair) {
      #(pair.0, shift_hvar_in_pattern(pair.1, shift))
    }))
    ast.PUnit -> pattern
    ast.PAny -> pattern
  }
}

fn get_span(term: ast.Term) -> Span {
  case term {
    ast.Typ(_, span) -> span
    ast.Lit(_, span) -> span
    ast.LitT(_, span) -> span
    ast.Var(_, span) -> span
    ast.Hole(_, span) -> span
    ast.Rcd(_, span) -> span
    ast.Ctr(_, _, span) -> span
    ast.Unit(span) -> span
    ast.Dot(_, _, span) -> span
    ast.Ann(_, _, span) -> span
    ast.Lam(_, _, _, span) -> span
    ast.Pi(_, _, _, _, span) -> span
    ast.App(_, _, _, span) -> span
    ast.Match(_, _, _, span) -> span
    ast.Call(_, _, span) -> span
    ast.Comptime(_, span) -> span
    ast.Fix(_, _, span) -> span
    ast.Let(_, _, _, span) -> span
    ast.Err(_, span) -> span
  }
}


// ============================================================================
// CHECK FUNCTIONS (needed by both infer and check modules)
// ============================================================================


// ============================================================================
// CHECK - Type Checking (bidirectional)
// ============================================================================

pub fn check(
  s: state.State,
  term: ast.Term,
  expected_ty: ast.Type,
  ty_span: Span,
) -> #(ast.Value, state.State) {
  case term {
    ast.Fix(name, body, span) -> {
      // For annotated Fix, use annotation type for def_var, not expected_ty.
      // This ensures the fix-bound name has the correct function type.
      case body {
        ast.Ann(_, ann_ty, _) -> {
          let #(fresh_ann_ty, _counter) = freshen_annotation(ann_ty, 0)
          let ann_ty_val = eval.eval(s.ffi, get_env(s), fresh_ann_ty)
          let env = get_env(s)
          let #(_fresh, s) = def_var(s, name, ann_ty_val)
          // Increment level for the body - it's in the scope of the fix-bound name
          let s = state.State(..s, level: s.level + 1)
          let #(body_val, s) = check(s, body, ann_ty_val, span)
          let s = state.State(..s, level: s.level - 1)
          let fix_val = ast.VFix(name, env, body)
          #(fix_val, s)
        }
        _ -> {
          // No annotation: use expected type
          let env = get_env(s)
          let #(_fresh, s) = def_var(s, name, expected_ty)
          // Increment level for the body - it's in the scope of the fix-bound name
          let s = state.State(..s, level: s.level + 1)
          let #(body_val, s) = check(s, body, expected_ty, span)
          let s = state.State(..s, level: s.level - 1)
          let fix_val = ast.VFix(name, env, body)
          #(fix_val, s)
        }
      }
    }
    ast.Lam(implicit, param, body, span) -> {
      case expected_ty {
        ast.VPi(exp_implicit, exp_name, pi_env, domain, codomain) -> {
          let #(_fresh, s) = def_var(s, param.0, domain)
          // Increment level for the body - it's in the scope of the bound parameter
          let s = state.State(..s, level: s.level + 1)
          let codomain_val = eval(s.ffi, get_env(s), codomain)
          let #(body_val, s) = check(s, body, codomain_val, span)
          let s = state.State(..s, level: s.level - 1)
          let lam_val = ast.VLam(implicit, param.0, get_env(s), body)
          #(lam_val, s)
        }
        _ -> {
          let #(value, inferred_ty, s) = infer(s, term)
          case inferred_ty, expected_ty {
            ast.VErr, _ | _, ast.VErr -> #(ast.VErr, s)
            _, _ -> {
              case unify.unify_result(s, inferred_ty, expected_ty, Span("", 0, 0, 0, 0), ty_span) {
                Ok(s) -> #(subst.force(s.ffi, s.subst, value), s)
                Error(e) -> #(ast.VErr, state.with_err(s, e))
              }
            }
          }
        }
      }
    }
    ast.Let(name, value, body, span) -> {
      let #(val_val, s1) = check(s, value, expected_ty, span)
      // For Let, we don't know the value type precisely yet - infer it
      let #(inferred_val, inferred_ty, s2) = infer(s1, value)
      let #(_fresh, s2) = def_var(s2, name, inferred_ty)
      let s3 = state.State(..s2, level: s2.level + 1)
      let #(body_val, s4) = check(s3, body, expected_ty, span)
      let s5 = state.State(..s4, level: s4.level - 1)
      #(body_val, s5)
    }
    _ -> {
      let #(value, inferred_ty, s) = infer(s, term)
      case inferred_ty, expected_ty {
        ast.VErr, _ | _, ast.VErr -> #(ast.VErr, s)
        _, _ -> {
          case unify.unify_result(s, inferred_ty, expected_ty, Span("", 0, 0, 0, 0), ty_span) {
            Ok(s) -> #(subst.force(s.ffi, s.subst, value), s)
            Error(e) -> #(ast.VErr, state.with_err(s, e))
          }
        }
      }
    }
  }
}

pub fn check_ctr_def(
  s: state.State,
  ctr: ast.CtrDef,
) -> #(List(Int), ast.Value, ast.Value, state.State) {
  let #(params, s) =
    list.fold(ctr.params, #([], s), fn(acc, name) {
      let #(params, s) = acc
      let id = s.hole_counter
      let #(hole, s) = new_hole_value(s)
      let params = [id, ..params]
      let s = state.State(..s, vars: [#(name, #(hole, hole)), ..s.vars])
      #(params, s)
    })

  let arg_ty = subst_param_vars(ctr.arg_ty, params, s)
  let ret_ty = subst_param_vars(ctr.ret_ty, params, s)

  #(params, arg_ty, ret_ty, s)
}

fn subst_param_vars(term: ast.Term, params: List(Int), s: state.State) -> ast.Value {
  case term {
    ast.Var(index, _) -> {
      case get_param_hole(params, index, s) {
        Some(hole_val) -> hole_val
        None -> eval(s.ffi, get_env(s), term)
      }
    }
    ast.Typ(k, _) -> ast.VTyp(k)
    ast.Lit(k, _) -> ast.VLit(k)
    ast.LitT(k, _) -> ast.VLitT(k)
    ast.Unit(_) -> ast.VUnit
    ast.Hole(id, _) -> ast.VNeut(ast.HHole(id), [])
    ast.Ann(inner, _, _) -> subst_param_vars(inner, params, s)
    ast.Lam(_, _, body, _) -> subst_param_vars(body, params, s)
    ast.Pi(_, _, in_term, out_term, _) -> {
      subst_param_vars(out_term, params, s)
    }
    ast.App(fun, _, arg, _) -> {
      subst_param_vars(fun, params, s)
    }
    ast.Rcd(fields, _) -> {
      ast.VRcd(list.map(fields, fn(pair) {
        #(pair.0, subst_param_vars(pair.1, params, s))
      }))
    }
    ast.Ctr(tag, arg, _) -> {
      ast.VCtrValue(ast.VCtr(tag, subst_param_vars(arg, params, s)))
    }
    ast.Dot(arg, name, _) -> {
      ast.VNeut(ast.HVar(0), [ast.EDot(name)])
    }
    ast.Match(_, motive, cases, _) -> {
      subst_param_vars(motive, params, s)
    }
    ast.Call(_, _, _) -> ast.VErr
    ast.Comptime(inner, _) -> subst_param_vars(inner, params, s)
    ast.Fix(_, body, _) -> subst_param_vars(body, params, s)
    ast.Let(_, value, body, _) -> {
      // For Let, substitute in the body (the value is already evaluated)
      subst_param_vars(body, params, s)
    }
    ast.Err(_, _) -> ast.VErr
  }
}

/// Shift HVar indices in a value down by 1.
/// Used when a nested lambda's body references outer bindings.
fn shift_hvar_down(value: ast.Value) -> ast.Value {
  shift_hvar_down_loop(value, 0)
}

fn shift_hvar_down_loop(value: ast.Value, offset: Int) -> ast.Value {
  case value {
    ast.VNeut(ast.HHole(id), spine) ->
      ast.VNeut(ast.HHole(id), list.map(spine, fn(e) { shift_hvar_down_elim(e, offset) }))
    ast.VNeut(ast.HVar(level), spine) ->
      case level > offset {
        True -> ast.VNeut(ast.HVar(level - 1), list.map(spine, fn(e) { shift_hvar_down_elim(e, offset) }))
        False -> ast.VNeut(ast.HVar(level), list.map(spine, fn(e) { shift_hvar_down_elim(e, offset) }))
      }
    ast.VNeut(head, spine) ->
      ast.VNeut(head, list.map(spine, fn(e) { shift_hvar_down_elim(e, offset) }))
    ast.VLam(impl, name, env, body) ->
      ast.VLam(impl, name, env, shift_hvar_down_term(body, offset + 1))
    ast.VPi(impl, name, env, in_val, out) ->
      ast.VPi(impl, name, env, shift_hvar_down_loop(in_val, offset), shift_hvar_down_term(out, offset))
    ast.VRcd(fields) ->
      ast.VRcd(list.map(fields, fn(kv) { #(kv.0, shift_hvar_down_loop(kv.1, offset)) }))
    ast.VCtrValue(ast.VCtr(tag, arg)) ->
      ast.VCtrValue(ast.VCtr(tag, shift_hvar_down_loop(arg, offset)))
    ast.VCall(name, args) ->
      ast.VCall(name, list.map(args, fn(a) { shift_hvar_down_loop(a, offset) }))
    ast.VFix(name, env, body) ->
      ast.VFix(name, env, shift_hvar_down_term(body, offset))
    ast.VRecord(fields) ->
      ast.VRcd(list.map(fields, fn(kv) { #(kv.0, shift_hvar_down_loop(kv.1, offset)) }))
    _ -> value
  }
}

fn shift_hvar_down_elim(elim: ast.Elim, offset: Int) -> ast.Elim {
  case elim {
    ast.EDot(name) -> ast.EDot(name)
    ast.EApp(arg) -> ast.EApp(shift_hvar_down_loop(arg, offset))
    ast.EAppImplicit(arg) -> ast.EAppImplicit(shift_hvar_down_loop(arg, offset))
    ast.EMatch(env, motive, cases) ->
      ast.EMatch(env, shift_hvar_down_loop(motive, offset), cases)
  }
}

fn shift_hvar_down_term(term: ast.Term, offset: Int) -> ast.Term {
  case term {
    ast.Hole(id, span) -> ast.Hole(id, span)
    ast.Var(index, span) ->
      case index > offset {
        True -> ast.Var(index - 1, span)
        False -> ast.Var(index, span)
      }
    ast.Lam(impl, param, body, span) ->
      ast.Lam(impl, param, shift_hvar_down_term(body, offset + 1), span)
    ast.Pi(impl, name, in_t, out_t, span) ->
      ast.Pi(impl, name, shift_hvar_down_term(in_t, offset), shift_hvar_down_term(out_t, offset + 1), span)
    ast.App(fun, impl, arg, span) ->
      ast.App(shift_hvar_down_term(fun, offset), list.map(impl, fn(t) { shift_hvar_down_term(t, offset) }), shift_hvar_down_term(arg, offset), span)
    ast.Rcd(fields, span) ->
      ast.Rcd(list.map(fields, fn(kv) { #(kv.0, shift_hvar_down_term(kv.1, offset)) }), span)
    ast.Ctr(tag, arg, span) ->
      ast.Ctr(tag, shift_hvar_down_term(arg, offset), span)
    ast.Dot(arg, name, span) ->
      ast.Dot(shift_hvar_down_term(arg, offset), name, span)
    ast.Ann(term, typ, span) ->
      ast.Ann(shift_hvar_down_term(term, offset), shift_hvar_down_term(typ, offset), span)
    ast.Match(arg, motive, cases, span) ->
      ast.Match(shift_hvar_down_term(arg, offset), shift_hvar_down_term(motive, offset), list.map(cases, fn(c) { ast.Case(c.pattern, shift_hvar_down_term(c.body, offset), c.guard, c.span) }), span)
    ast.Call(name, args, span) ->
      ast.Call(name, list.map(args, fn(a) { shift_hvar_down_term(a, offset) }), span)
    ast.Comptime(inner, span) ->
      ast.Comptime(shift_hvar_down_term(inner, offset), span)
    ast.Fix(name, body, span) ->
      ast.Fix(name, shift_hvar_down_term(body, offset + 1), span)
    ast.Let(name, value, body, span) ->
      ast.Let(name, shift_hvar_down_term(value, offset), shift_hvar_down_term(body, offset + 1), span)
    ast.Typ(k, span) -> ast.Typ(k, span)
    ast.Lit(v, span) -> ast.Lit(v, span)
    ast.LitT(t, span) -> ast.LitT(t, span)
    ast.Unit(span) -> ast.Unit(span)
    ast.Err(msg, span) -> ast.Err(msg, span)
  }
}

/// Shift HVar indices in a value UP by shift_amount.
/// Used when a nested lambda's type needs to reference outer bindings.
fn shift_hvar_up(value: ast.Value, shift_amount: Int) -> ast.Value {
  shift_hvar_up_loop(value, shift_amount, 0)
}

fn shift_hvar_up_loop(value: ast.Value, shift_amount: Int, offset: Int) -> ast.Value {
  case value {
    ast.VNeut(ast.HHole(id), spine) ->
      ast.VNeut(ast.HHole(id), list.map(spine, fn(e) { shift_hvar_up_elim(e, shift_amount, offset) }))
    ast.VNeut(ast.HVar(level), spine) ->
      ast.VNeut(ast.HVar(level + shift_amount), list.map(spine, fn(e) { shift_hvar_up_elim(e, shift_amount, offset) }))
    ast.VNeut(head, spine) ->
      ast.VNeut(head, list.map(spine, fn(e) { shift_hvar_up_elim(e, shift_amount, offset) }))
    ast.VLam(impl, name, env, body) ->
      ast.VLam(impl, name, env, shift_hvar_up_term(body, shift_amount, offset + 1))
    ast.VPi(impl, name, env, in_val, out) ->
      ast.VPi(impl, name, env, shift_hvar_up_loop(in_val, shift_amount, offset), shift_hvar_up_term(out, shift_amount, offset))
    ast.VRcd(fields) ->
      ast.VRcd(list.map(fields, fn(kv) { #(kv.0, shift_hvar_up_loop(kv.1, shift_amount, offset)) }))
    ast.VCtrValue(ast.VCtr(tag, arg)) ->
      ast.VCtrValue(ast.VCtr(tag, shift_hvar_up_loop(arg, shift_amount, offset)))
    ast.VCall(name, args) ->
      ast.VCall(name, list.map(args, fn(a) { shift_hvar_up_loop(a, shift_amount, offset) }))
    ast.VFix(name, env, body) ->
      ast.VFix(name, env, shift_hvar_up_term(body, shift_amount, offset))
    ast.VRecord(fields) ->
      ast.VRcd(list.map(fields, fn(kv) { #(kv.0, shift_hvar_up_loop(kv.1, shift_amount, offset)) }))
    _ -> value
  }
}

fn shift_hvar_up_elim(elim: ast.Elim, shift_amount: Int, offset: Int) -> ast.Elim {
  case elim {
    ast.EDot(name) -> ast.EDot(name)
    ast.EApp(arg) -> ast.EApp(shift_hvar_up_loop(arg, shift_amount, offset))
    ast.EAppImplicit(arg) -> ast.EAppImplicit(shift_hvar_up_loop(arg, shift_amount, offset))
    ast.EMatch(env, motive, cases) ->
      ast.EMatch(env, shift_hvar_up_loop(motive, shift_amount, offset), cases)
  }
}

fn shift_hvar_up_term(term: ast.Term, shift_amount: Int, offset: Int) -> ast.Term {
  case term {
    ast.Hole(id, span) -> ast.Hole(id, span)
    ast.Var(index, span) -> ast.Var(index + shift_amount, span)
    ast.Lam(impl, param, body, span) ->
      ast.Lam(impl, param, shift_hvar_up_term(body, shift_amount, offset + 1), span)
    ast.Pi(impl, name, in_t, out_t, span) ->
      ast.Pi(impl, name, shift_hvar_up_term(in_t, shift_amount, offset), shift_hvar_up_term(out_t, shift_amount, offset + 1), span)
    ast.App(fun, impl, arg, span) ->
      ast.App(shift_hvar_up_term(fun, shift_amount, offset), list.map(impl, fn(t) { shift_hvar_up_term(t, shift_amount, offset) }), shift_hvar_up_term(arg, shift_amount, offset), span)
    ast.Rcd(fields, span) ->
      ast.Rcd(list.map(fields, fn(kv) { #(kv.0, shift_hvar_up_term(kv.1, shift_amount, offset)) }), span)
    ast.Ctr(tag, arg, span) ->
      ast.Ctr(tag, shift_hvar_up_term(arg, shift_amount, offset), span)
    ast.Dot(arg, name, span) ->
      ast.Dot(shift_hvar_up_term(arg, shift_amount, offset), name, span)
    ast.Ann(term, typ, span) ->
      ast.Ann(shift_hvar_up_term(term, shift_amount, offset), shift_hvar_up_term(typ, shift_amount, offset), span)
    ast.Match(arg, motive, cases, span) ->
      ast.Match(shift_hvar_up_term(arg, shift_amount, offset), shift_hvar_up_term(motive, shift_amount, offset), list.map(cases, fn(c) { ast.Case(c.pattern, shift_hvar_up_term(c.body, shift_amount, offset), c.guard, c.span) }), span)
    ast.Call(name, args, span) ->
      ast.Call(name, list.map(args, fn(a) { shift_hvar_up_term(a, shift_amount, offset) }), span)
    ast.Comptime(inner, span) ->
      ast.Comptime(shift_hvar_up_term(inner, shift_amount, offset), span)
    ast.Fix(name, body, span) ->
      ast.Fix(name, shift_hvar_up_term(body, shift_amount, offset + 1), span)
    ast.Let(name, value, body, span) ->
      ast.Let(name, shift_hvar_up_term(value, shift_amount, offset), shift_hvar_up_term(body, shift_amount, offset + 1), span)
    ast.Typ(k, span) -> ast.Typ(k, span)
    ast.Lit(v, span) -> ast.Lit(v, span)
    ast.LitT(t, span) -> ast.LitT(t, span)
    ast.Unit(span) -> ast.Unit(span)
    ast.Err(msg, span) -> ast.Err(msg, span)
  }
}

fn get_param_hole(params: List(Int), index: Int, s: state.State) -> Option(ast.Value) {
  get_param_hole_loop(params, index, 0, s)
}

fn get_param_hole_loop(
  params: List(Int),
  index: Int,
  current: Int,
  s: state.State,
) -> Option(ast.Value) {
  case params {
    [] -> None
    [param_id, ..rest] -> {
      case current == index {
        True -> {
          let hole_val = ast.VNeut(ast.HHole(param_id), [])
          Some(hole_val)
        }
        False -> get_param_hole_loop(rest, index, current + 1, s)
      }
    }
  }
}

pub fn check_type(
  s: state.State,
  t1: ast.Value,
  t2: ast.Value,
  t1_span: Span,
  t2_span: Span,
) -> #(state.State, List(#(String, ast.Value))) {
  let #(_subst, s) = unify.unify(s, 0, t1, t2, t1_span, t2_span)
  #(s, [])
}

fn new_hole_value(s: state.State) -> #(ast.Value, state.State) {
  let id = s.hole_counter
  let hole_val = ast.VNeut(ast.HHole(id), [])
  // Record the hole depth for proper generalization filtering
  let s = state.State(
    ..s,
    hole_counter: id + 1,
    hole_depths: [#(id, s.lambda_depth), ..s.hole_depths],
  )
  #(hole_val, s)
}

