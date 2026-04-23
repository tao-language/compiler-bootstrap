// Core unification - Higher-order unification with Occurs check
// Unifies two types, possibly with holes. Updates state with bindings.

import core/ast.{type Type, TVar, TPi, TForAll}
import core/state.{type State, bind_hole}
import gleam/list
import gleam/int

/// Unify two types, updating state with bindings
pub fn unify(state: State, t1: Type, t2: Type) -> Result(State, String) {
  case t1, t2 {
    TVar(id1), TVar(id2) if id1 == id2 -> Ok(state)
    TVar(id1), _ -> Ok(bind_hole(state, id1, t2))
    _, TVar(id) ->
      case lookup_hole(state, id) {
        Ok(typ) -> unify(state, t1, typ)
        Error(_) -> unify(state, t1, t2)
      }
    _, _ -> unify_simple(state, t1, t2)
  }
}

/// Simple unification for non-variable types
fn unify_simple(state: State, t1: Type, t2: Type) -> Result(State, String) {
  case t1, t2 {
    TPi(_, arg1, body1), TPi(_, arg2, body2) ->
      case unify(state, arg1, arg2) {
        Ok(st) -> unify(st, body1, body2)
        Error(e) -> Error(e)
      }
    TForAll(_, t1), TForAll(_, t2) -> unify(state, t1, t2)
    _, _ -> Error("Types don't unify: " <> type_to_string(t1) <> " vs " <> type_to_string(t2))
  }
}

/// Lookup a hole in the state
fn lookup_hole(state: State, id: Int) -> Result(Type, String) {
  case list.find(state.hole_bindings, fn(h) { h.0 == id }) {
    Ok(#(_, typ)) -> Ok(typ)
    Error(_) -> Error("Unknown hole: " <> int.to_string(id))
  }
}

/// Substitute variables in a type (De Bruijn level shifting)
pub fn substitute(state: State, typ: Type) -> Result(Type, String) {
  case typ {
    TVar(id) ->
      case list.find(state.hole_bindings, fn(h) { h.0 == id }) {
        Ok(#(_, binding)) -> Ok(binding)
        Error(_) -> Ok(typ)
      }
    TPi(name, arg, body) ->
      case substitute(state, arg) {
        Ok(sub_arg) ->
          case substitute(state, body) {
            Ok(sub_body) -> Ok(TPi(name, sub_arg, sub_body))
            Error(e) -> Error(e)
          }
        Error(e) -> Error(e)
      }
    TForAll(name, body) ->
      case substitute(state, body) {
        Ok(sub_body) -> Ok(TForAll(name, sub_body))
        Error(e) -> Error(e)
      }
  }
}

/// Type stringification for debugging
pub fn type_to_string(typ: Type) -> String {
  case typ {
    TVar(id) ->
      case id < 0 {
        True -> "??"
        False -> "a" <> int.to_string(id)
      }
    TPi(_, arg, body) ->
      "(" <> type_to_string(arg) <> " -> " <> type_to_string(body) <> ")"
    TForAll(_, body) ->
      "∀" <> type_to_string(body)
  }
}
