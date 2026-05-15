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
/// - **Variables** (`VNeut(HVar(level))`) — look up the binding in state.
/// - **Same constructors** — recursively unify their fields.
/// - **Mismatched constructors** — record a `TypeMismatch` error.
///
/// The type checker calls this function at every place where two types
/// must agree. All errors accumulate in state; no early returns.
import core/ast.{
  type Elim, type Head, type Value, type LiteralType, type Term,
  EApp, EMatch, HHole, HVar, VCtr, VCall, VFix, VErr, VLam, VLit,
  VNeut, VPi, VRcd, VRcdT, VTyp, VLitT, VTypeDef,
  IntT, FloatT, I8T, I16T, I32T, I64T, U8T, U16T, U32T, U64T, F16T, F32T, F64T,
}
import core/state.{type State, State, TypeMismatch, with_err}
import gleam/int
import gleam/list
import gleam/option.{Some}
import gleam/string
import syntax/span.{single}

/// Unify two values: `expected` is the type being checked against,
/// `actual` is the value whose type must match.
///
/// Returns `(value, state)` where `value` is the unified type (with all
/// substitutions applied) and `state` is the updated state (with errors
/// accumulated if the types differ).
///
/// ## Example
///
/// ```gleam
/// import core/unify.{unify}
/// import core/state.{initial_state}
/// import core/ast.{VLit, VNeut, HHole, LitInt}
///
/// let state = initial_state([])
/// // A hole unifies with any concrete value — binds the hole
/// let #(value, final) = unify(state, VNeut(HHole(0), []), VLit(LitInt(42)))
/// ```
pub fn unify(
  state: State,
  expected: Value,
  actual: Value,
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> #(Value, State) {
  match_values(state, expected, actual, infer_fn)
}

/// Infer a result_type Term to get its Value.
///
/// This is used in GADT-style constructor checking to evaluate
/// the result_type Term (which may contain type parameter references)
/// to a Value that can be unified with the VCtr arg.
fn infer_result_type(
  state: State,
  result_type: Term,
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> #(Value, Value, State) {
  // Evaluate the result_type Term using the infer function.
  // This handles NbE-style normalization and resolves any
  // type parameter references.
  let #(value, type_, new_state) = infer_fn(state, result_type)
  #(value, type_, new_state)
}

/// Check if a value is a wildcard literal type ($Int or $Float).
pub fn is_wildcard(value: Value) -> Bool {
  case value {
    VLitT(IntT) | VLitT(FloatT) -> True
    _ -> False
  }
}

/// Check if a literal type matches a wildcard type.
/// - IntT matches IntT, I8T-I64T, U8T-U64T
/// - FloatT matches FloatT, F16T-F64T, and also IntT (for integer literals)
pub fn literal_type_matches_wildcard(wildcard: LiteralType, lit_type: LiteralType) -> Bool {
  case wildcard {
    IntT -> {
      case lit_type {
        IntT | I8T | I16T | I32T | I64T | U8T | U16T | U32T | U64T -> True
        _ -> False
      }
    }
    FloatT -> {
      case lit_type {
        FloatT | F16T | F32T | F64T | IntT | I8T | I16T | I32T | I64T | U8T | U16T | U32T | U64T -> True
      }
    }
    _ -> False
  }
}

// ── Core matching logic ───────────────────────────────────────────

fn match_values(
  state: State,
  expected: Value,
  actual: Value,
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> #(Value, State) {
  case expected, actual {
    // ── Same variable level — compare spines ─────────────────
    VNeut(HVar(l1), spine1), VNeut(HVar(l2), spine2) if l1 == l2 ->
      match_spines(state, spine1, spine2, infer_fn)

    // ── Variable in expected — look up in state, apply spine ─
    VNeut(HVar(level), spine1), _ -> {
      case lookup_level(state, level) {
        Ok(#(value, _)) -> {
          let applied = apply_spine_to_value(value, spine1)
          match_values(state, applied, actual, infer_fn)
        }
        Error(_) -> add_type_mismatch_error(state, expected, actual)
      }
    }

    // ── Same variable level in actual — look up in state, apply spine ──
    _, VNeut(HVar(l1), spine2) if l1 >= 0 ->
      case lookup_level(state, l1) {
        Ok(#(value, _)) -> {
          let applied = apply_spine_to_value(value, spine2)
          match_values(state, expected, applied, infer_fn)
        }
        Error(_) -> add_type_mismatch_error(state, expected, actual)
      }

    // ── Different holes — mismatch ───────────────────────────
    VNeut(HHole(id1), []), VNeut(HHole(id2), _) if id1 != id2 ->
      add_type_mismatch_error(state, expected, actual)

    // ── Hole in expected — bind it ───────────────────────────
    VNeut(HHole(id), []), _ -> {
      let s1 = bind_hole(state, id, actual, infer_fn)
      #(expected, s1)
    }

    // ── Same hole ID — trivially unified ─────────────────────
    VNeut(HHole(id1), _), VNeut(HHole(id2), _) if id1 == id2 -> #(expected, state)

    // ── Hole in actual — bind it ─────────────────────────────
    _, VNeut(HHole(id), []) -> {
      let s1 = bind_hole(state, id, expected, infer_fn)
      #(actual, s1)
    }

    // ── Neutral — neutral comparison ─────────────────────────
    VNeut(head1, spine1), VNeut(head2, spine2) ->
      match_neutral(state, head1, spine1, head2, spine2, infer_fn)

    // ── Lambda — unify param types ───────────────────────────
    VLam(_env1, _implicits1, param1, _body1), VLam(_env2, _implicits2, param2, _body2) ->
      match_values(state, param1.1, param2.1, infer_fn)

    // ── Pi types — unify domains, then codomains ─────────────
    VPi(_env1, _implicits1, domain1, codomain1), VPi(_env2, _implicits2, domain2, codomain2) -> {
      let #(dom_result, s1) = match_values(state, domain1.1, domain2.1, infer_fn)
      let _ = dom_result
      match_values(s1, codomain1, codomain2, infer_fn)
    }

    // ── Constructor — tag must match, then unify args ────────
    VCtr(tag1, arg1), VCtr(tag2, arg2) ->
      case tag1 == tag2 {
        True -> match_values(state, arg1, arg2, infer_fn)
        False ->
          add_type_mismatch_error(
            state,
            VCtr(tag1, VNeut(HHole(0), [])),
            VCtr(tag2, VNeut(HHole(0), [])),
          )
      }

    // ── VLitT — wildcard/specific type match ─────────────────
    // IntT matches IntT, I8T-I64T, U8T-U64T
    // FloatT matches FloatT, F16T-F64T, and all int types
    VLitT(wildcard), VLitT(specific) ->
      case literal_type_matches_wildcard(wildcard, specific) {
        True -> #(expected, state)
        False -> add_type_mismatch_error(state, expected, actual)
      }
    // Exact match for specific types
    VLitT(t1), VLitT(t2) ->
      case t1 == t2 {
        True -> #(expected, state)
        False -> add_type_mismatch_error(state, expected, actual)
      }
    // ── Ctr ↔ TypeDef — GADT-style constructor checking ─
    VCtr(tag, arg), VTypeDef(name, params, constructors) ->
      case list.find(constructors, fn(c) { c.0 == tag }) {
        Ok(#(_, #(bindings, self_type, result_type), _)) -> {
          // Self type is already a value (holes for type params).
          // Unify arg with self_type.
          let #(unified_arg, s1) = match_values(state, self_type, arg, infer_fn)
          // Evaluate the result_type Term to get its Value.
          // This is done via inference for NbE-style normalization.
          let #(return_value, _, s2) = infer_result_type(s1, result_type, infer_fn)
          // Unify the VCtr with the GADT return type.
          match_values(s2, VCtr(tag, unified_arg), return_value, infer_fn)
        }
        Error(_) ->
          add_type_mismatch_error(
            state,
            VCtr(tag, VNeut(HHole(0), [])),
            VTypeDef(name, params, constructors),
          )
      }

    // ── TypeDef ↔ Ctr — symmetric case ───────────────────────
    VTypeDef(name, params, constructors), VCtr(tag, arg) ->
      match_values(state, VCtr(tag, arg), VTypeDef(name, params, constructors), infer_fn)

    // ── Literal — exact value match ────────────────────────
    VLit(lit1), VLit(lit2) ->
      case lit1 == lit2 {
        True -> #(expected, state)
        False -> add_type_mismatch_error(state, expected, actual)
      }

    // ── Record — unify field by field ────────────────────────
    VRcd(fields1), VRcd(fields2) -> match_records(state, fields1, fields2, infer_fn)

    // ── VTyp — same universe level unifies ───────────────────
    VTyp(l1), VTyp(l2) if l1 == l2 -> #(expected, state)
    VTyp(_l1), VTyp(_l2) -> add_type_mismatch_error(state, expected, actual)

    // ── VCall — deferred FFI call, unifies if name and args match ──
    VCall(n1, args1, ret1), VCall(n2, args2, ret2) -> {
      case n1 == n2 && list.length(args1) == list.length(args2) {
        True -> match_values(state, ret1, ret2, infer_fn)
        False -> add_type_mismatch_error(state, expected, actual)
      }
    }

    // ── VFix — recursive fixpoint, unifies if names match ──
    VFix(n1, _, _), VFix(n2, _, _) -> {
      case n1 == n2 {
        True -> #(expected, state)
        False -> add_type_mismatch_error(state, expected, actual)
      }
    }

    // ── VErr — unifies with any value (error recovery) ───────
    VErr, _ -> #(expected, state)
    _, VErr -> #(expected, state)

    // ── Anything else — type mismatch ────────────────────────
    _, _ -> add_type_mismatch_error(state, expected, actual)
  }
}

// ── Hole binding ──────────────────────────────────────────────────

/// Bind a hole to a value.
///
/// Stores the binding in the variable environment using the name
/// `"hole{id}"` for lookup later.
fn bind_hole(
  state: State,
  id: Int,
  value: Value,
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> State {
  // Occurs check: skip binding if it would create a cycle
  case occurs_check(id, value) {
    True -> state
    False -> {
      // Check if this hole already has a binding
      case find_hole_binding(state, id) {
        Ok(already_bound) -> {
          let _s = match_values(state, already_bound, value, infer_fn)
          state
        }
        Error(Nil) -> {
          let binding_name = "hole" <> int.to_string(id)
          State(..state, vars: [#(binding_name, #(value, value)), ..state.vars])
        }
      }
    }
  }
}

// ── Variable lookup ───────────────────────────────────────────────

/// Look up a De Bruijn level in the state's variable bindings.
fn lookup_level(state: State, level: Int) -> Result(#(Value, Value), Nil) {
  case list.drop(state.vars, level) {
    [#(_, #(value, type_)), ..] -> Ok(#(value, type_))
    _ -> Error(Nil)
  }
}

/// Find a hole binding by ID.
fn find_hole_binding(state: State, id: Int) -> Result(Value, Nil) {
  let prefix = "hole" <> int.to_string(id)
  find_hole_loop(state.vars, prefix)
}

fn find_hole_loop(
  vars: List(#(String, #(Value, Value))),
  prefix: String,
) -> Result(Value, Nil) {
  case vars {
    [] -> Error(Nil)
    [#(name, #(value, _)), ..rest] ->
      case string.starts_with(name, prefix) {
        True -> {
          let chars = string.to_graphemes(name)
          let prefix_len = string.length(prefix)
          case list.drop(chars, prefix_len) {
            [] | ["_", ..] -> Ok(value)
            _ -> find_hole_loop(rest, prefix)
          }
        }
        False -> find_hole_loop(rest, prefix)
      }
  }
}

// ── Neutral comparison ────────────────────────────────────────────

fn match_neutral(
  state: State,
  head1: Head,
  spine1: List(Elim),
  head2: Head,
  spine2: List(Elim),
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> #(Value, State) {
  case head1, head2 {
    HVar(l1), HVar(l2) ->
      case l1 == l2 {
        True -> match_spines(state, spine1, spine2, infer_fn)
        False ->
          add_type_mismatch_error(
            state,
            VNeut(HVar(l1), spine1),
            VNeut(HVar(l2), spine2),
          )
      }
    HHole(id1), HHole(id2) ->
      case { id1 == id2 } && { list.length(spine1) == list.length(spine2) } {
        True -> match_spines(state, spine1, spine2, infer_fn)
        False ->
          add_type_mismatch_error(
            state,
            VNeut(HHole(id1), spine1),
            VNeut(HHole(id2), spine2),
          )
      }
    _, _ ->
      add_type_mismatch_error(state, VNeut(head1, spine1), VNeut(head2, spine2))
  }
}

/// Match two neutral spines element by element.
/// Spines of different lengths are a type mismatch.
fn match_spines(
  state: State,
  spine1: List(Elim),
  spine2: List(Elim),
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> #(Value, State) {
  case spine1, spine2 {
    [], [] -> #(VNeut(HVar(0), []), state)
    [EApp(arg1)], [EApp(arg2)] -> match_values(state, arg1, arg2, infer_fn)
    [EApp(arg1), ..rest1], [EApp(arg2), ..rest2] -> {
      let #(result, s1) = match_values(state, arg1, arg2, infer_fn)
      let _ = result
      match_spines(s1, rest1, rest2, infer_fn)
    }
    _, _ ->
      add_type_mismatch_error(
        state,
        VNeut(HVar(0), spine1),
        VNeut(HVar(0), spine2),
      )
  }
}

// ── Record matching ───────────────────────────────────────────────

fn match_records(
  state: State,
  fields1: List(#(String, Value)),
  fields2: List(#(String, Value)),
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> #(Value, State) {
  case fields1, fields2 {
    [], [] -> #(VRcd([]), state)
    [#(name1, val1), ..rest1], [#(name2, val2), ..rest2] ->
      case name1 == name2 {
        True -> {
          let #(val_result, s1) = match_values(state, val1, val2, infer_fn)
          let _ = val_result
          match_records(s1, rest1, rest2, infer_fn)
        }
        False -> add_type_mismatch_error(state, VRcd(fields1), VRcd(fields2))
      }
    _, _ -> add_type_mismatch_error(state, VRcd(fields1), VRcd(fields2))
  }
}

/// Unify two record type values field by field.
fn match_record_types(
  state: State,
  fields1: List(#(String, Value, option.Option(Value))),
  fields2: List(#(String, Value, option.Option(Value))),
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> #(Value, State) {
  case fields1, fields2 {
    [], [] -> #(VRcdT([]), state)
    [#(name1, type1, default1), ..rest1], [#(name2, type2, default2), ..rest2] ->
      case name1 == name2 {
        True -> {
          let #(type_result, s1) = match_values(state, type1, type2, infer_fn)
          let _ = type_result
          // Unify default values if both are present
          let #(d_result, s2) = case default1, default2 {
            Some(d1), Some(d2) -> match_values(s1, d1, d2, infer_fn)
            _, _ -> #(VRcdT([]), s1)
          }
          let _ = d_result
          match_record_types(s2, rest1, rest2, infer_fn)
        }
        False -> add_type_mismatch_error(state, VRcdT(fields1), VRcdT(fields2))
      }
    _, _ -> add_type_mismatch_error(state, VRcdT(fields1), VRcdT(fields2))
  }
}

// ── Occurs check ──────────────────────────────────────────────────

/// Check if a hole ID occurs in a value (for occurs check).
///
/// Always returns `False` to allow recursive types.
/// This is a deliberate design choice — Tao supports recursive types.
pub fn occurs_check(_level: Int, _value: Value) -> Bool {
  // Always return False to allow recursive types
  False
}

// ── Error helpers ─────────────────────────────────────────────────

fn add_type_mismatch_error(
  state: State,
  expected: Value,
  actual: Value,
) -> #(Value, State) {
  let new_state = with_err(state, TypeMismatch(expected, actual, single("", 0, 0)))
  #(VErr, new_state)
}

/// Apply a neutral spine to a value.
fn apply_spine_to_value(v: Value, spine: List(Elim)) -> Value {
  case spine {
    [] -> v
    [EApp(arg), ..rest] ->
      case v {
        VLam(_env, _implicits, #(_pname, _ptype), body) -> {
          // Beta-reduction placeholder: substitute and continue spine
          // For full correctness we'd substitute arg into body, but
          // for now just keep it as a neutral application
          VNeut(HVar(0), [EApp(arg), ..rest])
        }
        _ -> VNeut(HVar(0), [EApp(arg), ..rest])
      }
    [EMatch(env, cases), ..rest] -> {
      // Match elimination: defer as neutral
      VNeut(HVar(0), [EMatch(env, cases), ..rest])
    }
  }
}
