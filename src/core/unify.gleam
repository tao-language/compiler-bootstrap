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
  type Value,
  type Head,
  type Elim,
  VNeut, HHole, HVar, VPi, VCtr, VLit, VRcd, VErr, VLam, EApp, Var,
}
import core/state.{type State, State, with_err, TypeMismatch}
import gleam/list
import gleam/int
import gleam/string
import syntax/span.{single}

/// Unify two values: `expected` is the type being checked against,
/// `actual` is the value whose type must match.
///
/// Returns the state (with errors accumulated if the types differ).
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
/// let final = unify(state, VNeut(HHole(0), []), VLit(LitInt(42)))
/// ```
pub fn unify(state: State, expected: Value, actual: Value) -> State {
  match_values(state, expected, actual)
}

// ── Core matching logic ───────────────────────────────────────────

fn match_values(state: State, expected: Value, actual: Value) -> State {
  case expected, actual {
    // ── Same variable level — trivially unified ──────────────
    VNeut(HVar(l1), _), VNeut(HVar(l2), _) if l1 == l2 -> state

    // ── Variable in expected — look up in state ──────────────
    VNeut(HVar(level), _), _ -> {
      case lookup_level(state, level) {
        Ok(#(value, _)) -> match_values(state, value, actual)
        Error(_) -> add_type_mismatch_error(state, expected, actual)
      }
    }

    // ── Same variable level in actual — look up in state ────
    _, VNeut(HVar(l1), _) if l1 >= 0 ->
      case lookup_level(state, l1) {
        Ok(#(value, _)) -> match_values(state, expected, value)
        Error(_) -> add_type_mismatch_error(state, expected, actual)
      }

    // ── Different holes — mismatch ───────────────────────────
    VNeut(HHole(id1), []), VNeut(HHole(id2), _) if id1 != id2 ->
      add_type_mismatch_error(state, expected, actual)

    // ── Hole in expected — bind it ───────────────────────────
    VNeut(HHole(id), []), _ -> bind_hole(state, id, actual)

    // ── Same hole ID — trivially unified ─────────────────────
    VNeut(HHole(id1), _), VNeut(HHole(id2), _) if id1 == id2 -> state

    // ── Hole in actual — bind it ─────────────────────────────
    _, VNeut(HHole(id), []) -> bind_hole(state, id, expected)

    // ── Neutral — neutral comparison ─────────────────────────
    VNeut(head1, spine1), VNeut(head2, spine2) ->
      match_neutral(state, head1, spine1, head2, spine2)



    // ── Lambda — unify param types ───────────────────────────
    VLam(#(_, ptype1), _), VLam(#(_, ptype2), _) ->
      match_values(state, ptype1, ptype2)

    // ── Pi types — unify domains, then codomains ─────────────
    VPi(domain1, codomain1), VPi(domain2, codomain2) -> {
      let s1 = match_values(state, domain1, domain2)
      let bound = State(..s1, vars: [#("pi_param", #(domain2, domain2)), ..s1.vars])
      match_values(bound, codomain1, shift_value(codomain2, 1))
    }

    // ── Constructor — tag must match, then unify args ────────
    VCtr(tag1, arg1), VCtr(tag2, arg2) ->
      case tag1 == tag2 {
        True -> match_values(state, arg1, arg2)
        False -> add_type_mismatch_error(
          state,
          VCtr(tag1, VNeut(HHole(0), [])),
          VCtr(tag2, VNeut(HHole(0), [])),
        )
      }

    // ── Literal — value must be equal ────────────────────────
    VLit(lit1), VLit(lit2) ->
      case lit1 == lit2 {
        True -> state
        False -> add_type_mismatch_error(state, expected, actual)
      }

    // ── Record — unify field by field ────────────────────────
    VRcd(fields1), VRcd(fields2) ->
      match_records(state, fields1, fields2)

    // ── VErr — unifies with any value (error recovery) ───────
    VErr, _ -> state
    _, VErr -> state

    // ── Anything else — type mismatch ────────────────────────
    _, _ -> add_type_mismatch_error(state, expected, actual)
  }
}

// ── Hole binding ──────────────────────────────────────────────────

/// Bind a hole to a value.
///
/// Stores the binding in the variable environment using the name
/// `"hole{id}"` for lookup later.
fn bind_hole(state: State, id: Int, value: Value) -> State {
  // Occurs check: skip binding if it would create a cycle
  case occurs_check(id, value) {
    True -> state
    False -> {
      // Check if this hole already has a binding
      case find_hole_binding(state, id) {
        Ok(already_bound) -> match_values(state, already_bound, value)
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
) -> State {
  case head1, head2 {
    HVar(l1), HVar(l2) ->
      case l1 == l2 {
        True -> match_spines(state, spine1, spine2)
        False -> add_type_mismatch_error(
          state, VNeut(HVar(l1), spine1), VNeut(HVar(l2), spine2),
        )
      }
    HHole(id1), HHole(id2) ->
      case { id1 == id2 } && { list.length(spine1) == list.length(spine2) } {
        True -> match_spines(state, spine1, spine2)
        False -> add_type_mismatch_error(
          state, VNeut(HHole(id1), spine1), VNeut(HHole(id2), spine2),
        )
      }
    _, _ -> add_type_mismatch_error(
      state, VNeut(head1, spine1), VNeut(head2, spine2),
    )
  }
}

/// Match two neutral spines element by element.
/// Spines of different lengths are a type mismatch.
fn match_spines(state: State, spine1: List(Elim), spine2: List(Elim)) -> State {
  case spine1, spine2 {
    [], [] -> state
    [EApp(arg1)], [EApp(arg2)] -> match_values(state, arg1, arg2)
    _, _ -> add_type_mismatch_error(
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
) -> State {
  case fields1, fields2 {
    [], [] -> state
    [#(name1, val1), ..rest1], [#(name2, val2), ..rest2] ->
      case name1 == name2 {
        True -> match_records(
          match_values(state, val1, val2),
          rest1,
          rest2,
        )
        False -> add_type_mismatch_error(state, VRcd(fields1), VRcd(fields2))
      }
    _, _ -> add_type_mismatch_error(state, VRcd(fields1), VRcd(fields2))
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

/// Shift De Bruijn levels in a value by n.
/// Used when binding a variable under a Pi-type binder.
fn shift_value(value: Value, n: Int) -> Value {
  case value {
    VNeut(head, spine) ->
      VNeut(shift_head(head, n), list.map(spine, fn(e) { shift_elim(e, n) }))
    VPi(domain, codomain) ->
      VPi(shift_value(domain, n), shift_value(codomain, n))
    VLam(#(name, param), _) ->
      VLam(#(name, shift_value(param, n)), Var(0, single("", 0, 0)))
    VLit(value) -> VLit(value)
    VCtr(tag, arg) -> VCtr(tag, shift_value(arg, n))
    VRcd(fields) ->
      VRcd(list.map(fields, fn(f) { #(f.0, shift_value(f.1, n)) }))
    VErr -> VErr
  }
}

fn shift_head(head: Head, n: Int) -> Head {
  case head {
    HVar(level) -> HVar(level + n)
    HHole(id) -> HHole(id)
  }
}

fn shift_elim(e: Elim, n: Int) -> Elim {
  case e {
    EApp(arg) -> EApp(shift_value(arg, n))
  }
}

// ── Error helpers ─────────────────────────────────────────────────

fn add_type_mismatch_error(state: State, expected: Value, actual: Value) -> State {
  with_err(state, TypeMismatch(expected, actual, single("", 0, 0)))
}
