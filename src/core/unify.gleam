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
import core/shift
import core/state.{type FFI, type State, State, TypeMismatch, with_err}
import core/unwrap
import core/utils
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span, Span}

/// Dummy span for use when no real span is available (e.g., EFix has no span).
const dummy_span = Span("unify", 0, 0, 0, 0)

/// Unify two lists of #(String, Value) by comparing both the name and the value.
fn unify_string_value_pairs(
  state: State,
  list1: List(#(String, ast.Value)),
  list2: List(#(String, ast.Value)),
  span: Span,
) -> State {
  case list1, list2 {
    [], [] -> state
    [a, ..rest1], [b, ..rest2] -> {
      case a.0 == b.0 {
        True -> {
          let state = unify_values(state, #(a.1, span), #(b.1, span))
          unify_string_value_pairs(state, rest1, rest2, span)
        }
        False -> with_err(state, TypeMismatch(#(a.1, span), #(b.1, span)))
      }
    }
    _, _ -> with_err(state, TypeMismatch(#(ast.VErr, span), #(ast.VErr, span)))
  }
}

/// Unify two values, recording mismatches as errors in the state.
///
/// Both values are force-normalized before comparison to resolve any
/// holes that have already been solved.
pub fn unify(
  state: State,
  a: #(ast.Value, Span),
  b: #(ast.Value, Span),
) -> State {
  let #(value1, span1) = a
  let #(value2, span2) = b

  // Force-normalize both values to resolve any solved holes.
  let value1 = unwrap.unwrap(state.ffi, state.subst, value1)
  let value2 = unwrap.unwrap(state.ffi, state.subst, value2)

  unify_values(state, #(value1, span1), #(value2, span2))
}

/// Unify two values after force-normalization.
fn unify_values(
  state: State,
  a: #(ast.Value, Span),
  b: #(ast.Value, Span),
) -> State {
  let #(value1, span1) = a
  let #(value2, span2) = b
  case value1, value2 {
    ast.VTyp(u1), ast.VTyp(u2) if u1 == u2 -> state
    ast.VLit(v1), ast.VLit(v2) if v1 == v2 -> state
    ast.VLitT(v1), ast.VLitT(v2) if v1 == v2 -> state
    ast.VCtr(t1, a1), ast.VCtr(t2, a2) if t1 == t2 ->
      unify_values(state, #(a1, span1), #(a2, span2))

    ast.VRcd(fields1), ast.VRcd(fields2) ->
      unify_rcd(state, fields1, fields2, span1)

    ast.VRcdT(fields1), ast.VRcdT(fields2) ->
      unify_rcd_type(state, fields1, fields2, span1)

    ast.VPi(imp1, dom1, cod1), ast.VPi(imp2, dom2, cod2) -> {
      let state = unify_string_value_pairs(state, imp1, imp2, span1)
      let state = unify_values(state, #(dom1.1, span1), #(dom2.1, span2))
      unify_values(state, #(cod1, span1), #(cod2, span2))
    }

    ast.VLam(env1, _, param1, body1), ast.VLam(env2, _, param2, body2) -> {
      // Evaluate both bodies with their respective environments to get Values,
      // then unify the resulting values.
      // The param gets a dummy value of vvar(0, []), shifted to account for
      // the env's existing binders.
      let param_val = ast.vvar(0, [])
      let shifted_param = shift.shift_value(param_val, list.length(env1))
      let env1_with_param = list.append(env1, [shifted_param])
      let body_val1 = eval_vlam_body(state.ffi, env1_with_param, body1)

      let shifted_param2 = shift.shift_value(param_val, list.length(env2))
      let env2_with_param = list.append(env2, [shifted_param2])
      let body_val2 = eval_vlam_body(state.ffi, env2_with_param, body2)

      unify_values(state, #(body_val1, span1), #(body_val2, span2))
    }

    ast.VTypeDef(params1, ctrs1), ast.VTypeDef(params2, ctrs2) -> {
      let state = unify_string_value_pairs(state, params1, params2, span1)
      unify_constructors(state, ctrs1, ctrs2, span1)
    }

    ast.VNeut(h1, spine1), ast.VNeut(h2, spine2) if h1 == h2 ->
      unify_spines(state, spine1, spine2)

    _, ast.VNeut(ast.HHole(id), _) -> solve_hole(state, #(id, span2), a)
    ast.VNeut(ast.HHole(id), _), _ -> solve_hole(state, #(id, span1), b)

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
          let state = unify_values(state, #(f1.1, span), #(f2.1, span))
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
          let state = unify_values(state, #(f1.1, span), #(f2.1, span))
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
    Some(v1), Some(v2) -> unify_values(state, #(v1, span), #(v2, span))
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

/// Unify two constructor lists for VTypeDef.
fn unify_constructors(
  state: State,
  ctrs1: List(#(String, #(List(String), ast.Value, ast.Term))),
  ctrs2: List(#(String, #(List(String), ast.Value, ast.Term))),
  span: Span,
) -> State {
  case ctrs1, ctrs2 {
    [], [] -> state
    [#(ctr_name1, #(param_names1, param_type1, _body1)), ..rest1],
      [#(ctr_name2, #(param_names2, param_type2, _body2)), ..rest2]
    -> {
      case ctr_name1 == ctr_name2 {
        True -> {
          // Unify the param types (single Value each)
          let state =
            unify_values(state, #(param_type1, span), #(param_type2, span))
          let state = unify_constructors(state, rest1, rest2, span)
          state
        }
        False ->
          with_err(state, TypeMismatch(#(ast.VErr, span), #(ast.VErr, span)))
      }
    }
    _, _ -> with_err(state, TypeMismatch(#(ast.VErr, span), #(ast.VErr, span)))
  }
}

/// Unify a list of value pairs.
fn unify_value_list(
  state: State,
  pairs: List(#(ast.Value, ast.Value)),
  span: Span,
) -> State {
  case pairs {
    [] -> state
    [#(v1, v2), ..rest] -> {
      let state = unify_values(state, #(v1, span), #(v2, span))
      unify_value_list(state, rest, span)
    }
  }
}

/// Solve a hole by binding it to a value, with occur-check.
///
/// An occur-check prevents binding a hole to a value that contains
/// the hole itself, which would create a cyclic substitution and
/// cause infinite loops during normalization.
fn solve_hole(state: State, a: #(Int, Span), b: #(ast.Value, Span)) -> State {
  let #(hole_id, span1) = a
  let #(value, span2) = b

  // First, force-normalize the value to resolve any inner holes.
  let value = unwrap.unwrap(state.ffi, state.subst, value)

  // Check if the hole already has a substitution.
  case list.key_find(state.subst, hole_id) {
    Ok(solution) -> unify_values(state, #(solution, span1), b)
    Error(Nil) -> {
      // Occur-check: ensure the hole doesn't appear in the value.
      case occurs_in(hole_id, value) {
        True -> {
          // Cyclic reference detected; record an error instead of binding.
          with_err(
            state,
            TypeMismatch(#(value, span2), #(
              ast.VNeut(ast.HHole(hole_id), []),
              span1,
            )),
          )
        }
        False -> {
          // Bind the hole to the normalized value.
          State(..state, subst: [#(hole_id, value), ..state.subst])
        }
      }
    }
  }
}

/// Check whether `hole_id` appears anywhere in `value`.
///
/// This is used for the occur-check during hole solving.
fn occurs_in(hole_id: Int, value: ast.Value) -> Bool {
  case value {
    ast.VTyp(_) -> False
    ast.VLit(_) -> False
    ast.VLitT(_) -> False
    ast.VErr -> False

    ast.VCtr(_, arg) -> occurs_in(hole_id, arg)

    ast.VRcd(fields) -> list.any(fields, fn(f) { occurs_in(hole_id, f.1) })

    ast.VRcdT(fields) ->
      list.any(fields, fn(f) {
        occurs_in(hole_id, f.1)
        || case f.2 {
          None -> False
          Some(v) -> occurs_in(hole_id, v)
        }
      })

    ast.VPi(implicits, domain, codomain) -> {
      list.any(implicits, fn(i) { occurs_in(hole_id, i.1) })
      || occurs_in(hole_id, domain.1)
      || occurs_in(hole_id, codomain)
    }

    ast.VLam(env, _, _, _) -> list.any(env, fn(v) { occurs_in(hole_id, v) })

    ast.VTypeDef(params, _) ->
      list.any(params, fn(p) { occurs_in(hole_id, p.1) })

    ast.VNeut(head, spine) -> {
      occurs_in_head(hole_id, head)
      || list.any(spine, fn(e) { occurs_in_elim(hole_id, e) })
    }
  }
}

fn occurs_in_head(hole_id: Int, head: ast.Head) -> Bool {
  case head {
    ast.HVar(_) -> False
    ast.HHole(id) -> id == hole_id
    ast.HCall(_, args) -> list.any(args, fn(a) { occurs_in(hole_id, a) })
  }
}

fn occurs_in_elim(hole_id: Int, elim: ast.Elim) -> Bool {
  case elim {
    ast.EApp(arg, _) -> occurs_in(hole_id, arg)
    ast.EMatch(env, _, _) -> list.any(env, fn(v) { occurs_in(hole_id, v) })
    ast.EFix(env, _) -> list.any(env, fn(v) { occurs_in(hole_id, v) })
  }
}

/// Unify two neutral term spines element-wise.
fn unify_spines(
  state: State,
  spine1: List(ast.Elim),
  spine2: List(ast.Elim),
) -> State {
  case spine1, spine2 {
    [], [] -> state
    [a, ..rest1], [b, ..rest2] -> {
      let state = unify_elim(state, a, b)
      unify_spines(state, rest1, rest2)
    }
    _, _ -> with_err(state, state.SpineArityMismatch(spine1, spine2))
  }
}

/// Unify two eliminators.
fn unify_elim(state: State, elim1: ast.Elim, elim2: ast.Elim) -> State {
  case elim1, elim2 {
    ast.EApp(arg1, span1), ast.EApp(arg2, span2) ->
      unify_values(state, #(arg1, span1), #(arg2, span2))

    ast.EMatch(env1, cases1, elim_span1), ast.EMatch(env2, cases2, elim_span2)
    -> {
      // Unify match environments.
      let state = unify_value_list(state, list.zip(env1, env2), elim_span1)

      // Unify match cases by pattern and body.
      unify_match_cases(state, cases1, cases2, elim_span1)
    }

    ast.EFix(env1, body1), ast.EFix(env2, body2) -> {
      // Unify fixpoint environments.
      let state = unify_value_list(state, list.zip(env1, env2), dummy_span)

      // Compare bodies structurally (both are Terms in De Bruijn indices).
      unify_terms(state, body1, body2, dummy_span)
    }

    _, _ -> with_err(state, state.SpineElimMismatch(elim1, elim2))
  }
}

/// Unify two match case lists.
fn unify_match_cases(
  state: State,
  cases1: List(ast.Case),
  cases2: List(ast.Case),
  span: Span,
) -> State {
  case cases1, cases2 {
    [], [] -> state
    [c1, ..rest1], [c2, ..rest2] -> {
      let state = unify_match_case(state, c1, c2, span)
      unify_match_cases(state, rest1, rest2, span)
    }
    _, _ -> with_err(state, TypeMismatch(#(ast.VErr, span), #(ast.VErr, span)))
  }
}

/// Unify two match cases.
fn unify_match_case(
  state: State,
  c1: ast.Case,
  c2: ast.Case,
  span: Span,
) -> State {
  // Compare patterns structurally (patterns are value-level constructs).
  let state = unify_patterns(state, c1.pattern, c2.pattern, span)

  // Compare guards if both present.
  let state = case c1.guard, c2.guard {
    Some(#(g1, _)), Some(#(g2, _)) -> unify_terms(state, g1, g2, span)
    None, None -> state
    _, _ -> with_err(state, TypeMismatch(#(ast.VErr, span), #(ast.VErr, span)))
  }

  // Compare bodies.
  unify_terms(state, c1.body, c2.body, span)
}

/// Unify two patterns structurally.
fn unify_patterns(
  state: State,
  p1: ast.Pattern,
  p2: ast.Pattern,
  span: Span,
) -> State {
  case p1, p2 {
    ast.PAny(_), ast.PAny(_) -> state
    ast.PTyp(u1, _), ast.PTyp(u2, _) if u1 == u2 -> state
    ast.PLit(v1, _), ast.PLit(v2, _) if v1 == v2 -> state
    ast.PLitT(t1, _), ast.PLitT(t2, _) if t1 == t2 -> state
    ast.PAlias(n1, pat1, _), ast.PAlias(n2, pat2, _) if n1 == n2 ->
      unify_patterns(state, pat1, pat2, span)
    ast.PCtr(tag1, pat1, _), ast.PCtr(tag2, pat2, _) if tag1 == tag2 ->
      unify_patterns(state, pat1, pat2, span)
    ast.PRcd(fields1, _), ast.PRcd(fields2, _) ->
      unify_rcd_patterns(state, fields1, fields2, span)
    ast.PError(_), ast.PError(_) -> state
    _, _ -> with_err(state, TypeMismatch(#(ast.VErr, span), #(ast.VErr, span)))
  }
}

/// Unify two record pattern field lists.
fn unify_rcd_patterns(
  state: State,
  fields1: List(#(String, ast.Pattern)),
  fields2: List(#(String, ast.Pattern)),
  span: Span,
) -> State {
  case fields1, fields2 {
    [], [] -> state
    [f1, ..rest1], [f2, ..rest2] -> {
      case f1.0 == f2.0 {
        True -> {
          let state = unify_patterns(state, f1.1, f2.1, span)
          unify_rcd_patterns(state, rest1, rest2, span)
        }
        False ->
          with_err(state, TypeMismatch(#(ast.VErr, span), #(ast.VErr, span)))
      }
    }
    _, _ -> with_err(state, TypeMismatch(#(ast.VErr, span), #(ast.VErr, span)))
  }
}

/// Unify two terms structurally (for comparing match bodies, guards, etc.).
fn unify_terms(state: State, t1: ast.Term, t2: ast.Term, span: Span) -> State {
  case t1, t2 {
    ast.Typ(u1, s1), ast.Typ(u2, _) if u1 == u2 -> state
    ast.Lit(v1, s1), ast.Lit(v2, _) if v1 == v2 -> state
    ast.LitT(t1, s1), ast.LitT(t2, _) if t1 == t2 -> state
    ast.Var(i1, _), ast.Var(i2, _) if i1 == i2 -> state
    ast.Hole(id1, _), ast.Hole(id2, _) if id1 == id2 -> state
    ast.Ctr(tag1, arg1, _), ast.Ctr(tag2, arg2, _) if tag1 == tag2 ->
      unify_terms(state, arg1, arg2, span)
    ast.Rcd(f1, _), ast.Rcd(f2, _) -> unify_terms_rcd(state, f1, f2, span)
    ast.RcdT(f1, _), ast.RcdT(f2, _) ->
      unify_terms_rcd_type(state, f1, f2, span)
    ast.Call(n1, a1, r1, _), ast.Call(n2, a2, r2, _)
      if n1 == n2 && a1 == a2 && r1 == r2
    -> state
    ast.Ann(term1, type1, _), ast.Ann(term2, type2, _) -> {
      let state = unify_terms(state, term1, term2, span)
      unify_terms(state, type1, type2, span)
    }
    ast.Lam(i1, p1, b1, _), ast.Lam(i2, p2, b2, _) -> {
      let state = unify_terms_lam_implicits(state, i1, i2, span)
      let state = unify_terms(state, p1.1, p2.1, span)
      unify_terms(state, b1, b2, span)
    }
    ast.Pi(i1, d1, c1, _), ast.Pi(i2, d2, c2, _) -> {
      let state = unify_terms_pi_implicits(state, i1, i2, span)
      let state = unify_terms(state, d1.1, d2.1, span)
      unify_terms(state, c1, c2, span)
    }
    ast.Fix(n1, b1, _), ast.Fix(n2, b2, _) if n1 == n2 ->
      unify_terms(state, b1, b2, span)
    ast.App(f1, a1, _), ast.App(f2, a2, _) -> {
      let state = unify_terms(state, f1, f2, span)
      unify_terms(state, a1, a2, span)
    }
    ast.TypeDef(p1, c1, _), ast.TypeDef(p2, c2, _) -> {
      let state = unify_terms_type_def_params(state, p1, p2, span)
      unify_terms_type_def_ctrs(state, c1, c2, span)
    }
    ast.Match(arg1, cases1, _), ast.Match(arg2, cases2, _) -> {
      let state = unify_terms(state, arg1, arg2, span)
      unify_terms_match_cases(state, cases1, cases2, span)
    }
    ast.Err(_), ast.Err(_) -> state
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
          ast.VNeut(ast.HVar(0), []),
          span,
        )),
      )
  }
}

fn unify_terms_rcd(
  state: State,
  fields1: List(#(String, ast.Term)),
  fields2: List(#(String, ast.Term)),
  span: Span,
) -> State {
  case fields1, fields2 {
    [], [] -> state
    [f1, ..rest1], [f2, ..rest2] -> {
      case f1.0 == f2.0 {
        True -> {
          let state = unify_terms(state, f1.1, f2.1, span)
          unify_terms_rcd(state, rest1, rest2, span)
        }
        False ->
          with_err(
            state,
            TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
              ast.VNeut(ast.HVar(0), []),
              span,
            )),
          )
      }
    }
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
          ast.VNeut(ast.HVar(0), []),
          span,
        )),
      )
  }
}

fn unify_terms_rcd_type(
  state: State,
  fields1: List(#(String, ast.Term, Option(ast.Term))),
  fields2: List(#(String, ast.Term, Option(ast.Term))),
  span: Span,
) -> State {
  case fields1, fields2 {
    [], [] -> state
    [f1, ..rest1], [f2, ..rest2] -> {
      case f1.0 == f2.0 {
        True -> {
          let state = unify_terms(state, f1.1, f2.1, span)
          let state = unify_terms_option(state, f1.2, f2.2, span)
          unify_terms_rcd_type(state, rest1, rest2, span)
        }
        False ->
          with_err(
            state,
            TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
              ast.VNeut(ast.HVar(0), []),
              span,
            )),
          )
      }
    }
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
          ast.VNeut(ast.HVar(0), []),
          span,
        )),
      )
  }
}

fn unify_terms_option(
  state: State,
  opt1: Option(ast.Term),
  opt2: Option(ast.Term),
  span: Span,
) -> State {
  case opt1, opt2 {
    Some(t1), Some(t2) -> unify_terms(state, t1, t2, span)
    None, None -> state
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
          ast.VNeut(ast.HVar(0), []),
          span,
        )),
      )
  }
}

fn unify_terms_lam_implicits(
  state: State,
  i1: List(#(String, ast.Term)),
  i2: List(#(String, ast.Term)),
  span: Span,
) -> State {
  case i1, i2 {
    [], [] -> state
    [a, ..rest1], [b, ..rest2] -> {
      case a.0 == b.0 {
        True -> {
          let state = unify_terms(state, a.1, b.1, span)
          unify_terms_lam_implicits(state, rest1, rest2, span)
        }
        False ->
          with_err(
            state,
            TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
              ast.VNeut(ast.HVar(0), []),
              span,
            )),
          )
      }
    }
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
          ast.VNeut(ast.HVar(0), []),
          span,
        )),
      )
  }
}

fn unify_terms_pi_implicits(
  state: State,
  i1: List(#(String, ast.Term)),
  i2: List(#(String, ast.Term)),
  span: Span,
) -> State {
  case i1, i2 {
    [], [] -> state
    [a, ..rest1], [b, ..rest2] -> {
      case a.0 == b.0 {
        True -> {
          let state = unify_terms(state, a.1, b.1, span)
          unify_terms_pi_implicits(state, rest1, rest2, span)
        }
        False ->
          with_err(
            state,
            TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
              ast.VNeut(ast.HVar(0), []),
              span,
            )),
          )
      }
    }
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
          ast.VNeut(ast.HVar(0), []),
          span,
        )),
      )
  }
}

fn unify_terms_type_def_params(
  state: State,
  p1: List(#(String, ast.Term)),
  p2: List(#(String, ast.Term)),
  span: Span,
) -> State {
  case p1, p2 {
    [], [] -> state
    [a, ..rest1], [b, ..rest2] -> {
      case a.0 == b.0 {
        True -> {
          let state = unify_terms(state, a.1, b.1, span)
          unify_terms_type_def_params(state, rest1, rest2, span)
        }
        False ->
          with_err(
            state,
            TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
              ast.VNeut(ast.HVar(0), []),
              span,
            )),
          )
      }
    }
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
          ast.VNeut(ast.HVar(0), []),
          span,
        )),
      )
  }
}

fn unify_terms_type_def_ctrs(
  state: State,
  c1: List(#(String, #(List(String), ast.Term, ast.Term), Span)),
  c2: List(#(String, #(List(String), ast.Term, ast.Term), Span)),
  span: Span,
) -> State {
  case c1, c2 {
    [], [] -> state
    [#(ctr_name1, #(param_names1, param_type1, body1), _span1), ..rest1],
      [#(ctr_name2, #(param_names2, param_type2, body2), _span2), ..rest2]
    -> {
      case ctr_name1 == ctr_name2 {
        True -> {
          let state = unify_terms(state, param_type1, param_type2, span)
          unify_terms_type_def_ctrs(state, rest1, rest2, span)
        }
        False ->
          with_err(
            state,
            TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
              ast.VNeut(ast.HVar(0), []),
              span,
            )),
          )
      }
    }
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
          ast.VNeut(ast.HVar(0), []),
          span,
        )),
      )
  }
}

fn unify_terms_match_cases(
  state: State,
  c1: List(ast.Case),
  c2: List(ast.Case),
  span: Span,
) -> State {
  case c1, c2 {
    [], [] -> state
    [a, ..rest1], [b, ..rest2] -> {
      let state = unify_terms(state, a.body, b.body, span)
      unify_terms_match_cases(state, rest1, rest2, span)
    }
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
          ast.VNeut(ast.HVar(0), []),
          span,
        )),
      )
  }
}

fn unify_terms_list(
  state: State,
  t1: List(ast.Term),
  t2: List(ast.Term),
  span: Span,
) -> State {
  case t1, t2 {
    [], [] -> state
    [a, ..rest1], [b, ..rest2] -> {
      let state = unify_terms(state, a, b, span)
      unify_terms_list(state, rest1, rest2, span)
    }
    _, _ ->
      with_err(
        state,
        TypeMismatch(#(ast.VNeut(ast.HVar(0), []), span), #(
          ast.VNeut(ast.HVar(0), []),
          span,
        )),
      )
  }
}

/// Evaluate a VLam's body in its environment with the param prepended.
/// The param is given a dummy value of vvar(0, []), shifted to account
/// for the env's existing binders so that indices stay coherent.
fn eval_vlam_body(ffi: FFI, env: ast.Env, body: ast.Term) -> ast.Value {
  eval.eval(ffi, env, body)
}
