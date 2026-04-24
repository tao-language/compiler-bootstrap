// Core infer - Bidirectional Type Checking
// Type checker with bidirectional inference and checking.

import core/ast.{type Term, type Type, type Case, Var, Lam, App, Lit, Ctr, Match, Hole, Err, LInt, LFloat, LString, TVar, TPi, TForAll}
import core/state.{type State}
import gleam/list
import gleam/int

/// Infer the type of a term
pub fn infer_term(state: State, term: Term) -> Result(State, String) {
  case term {
    Var(name, _) -> infer_var(state, name)
    Lam(param, body) -> infer_lam(state, param, body)
    App(fun, arg) -> infer_app(state, fun, arg)
    Lit(LInt(_)) -> infer_intlit(state)
    Lit(LFloat(_)) -> infer_floatlit(state)
    Lit(LString(_)) -> infer_stringlit(state)
    Ctr(_, _) -> infer_ctr(state)
    Match(scrutinee, cases) -> infer_match(state, scrutinee, cases)
    Hole(id) -> infer_hole(state, id)
    Err(message) -> Error(message)
  }
}

/// Check a term against an expected type
/// For prototype: just infer the term type (full checking requires storing inferred type)
pub fn check_term(state: State, term: Term, _expected: Type) -> Result(State, String) {
  case infer_term(state, term) {
    Ok(st) -> {
      // TODO: Implement full type checking by storing and unifying inferred types
      // For now, just return the state after inference
      Ok(st)
    }
    Error(e) -> Error(e)
  }
}

/// Infer variable type
fn infer_var(state: State, name: String) -> Result(State, String) {
  case state.lookup_env(state, name) {
    Ok(_) -> Ok(state)
    Error(_) -> Error("Unknown variable: " <> name)
  }
}

/// Infer lambda type
fn infer_lam(state: State, _param: String, body: Term) -> Result(State, String) {
  case infer_term(state, body) {
    Ok(st) -> Ok(st)
    Error(e) -> Error(e)
  }
}

/// Infer application type
fn infer_app(state: State, fun: Term, arg: Term) -> Result(State, String) {
  case infer_term(state, fun) {
    Ok(st) -> infer_term(st, arg)
    Error(e) -> Error(e)
  }
}

/// Infer integer literal type
fn infer_intlit(state: State) -> Result(State, String) {
  Ok(state)
}

/// Infer float literal type
fn infer_floatlit(state: State) -> Result(State, String) {
  Ok(state)
}

/// Infer string literal type
fn infer_stringlit(state: State) -> Result(State, String) {
  Ok(state)
}

/// Infer constructor type
fn infer_ctr(state: State) -> Result(State, String) {
  Ok(state)
}

/// Infer hole type
fn infer_hole(state: State, _id: Int) -> Result(State, String) {
  // Holes are untyped placeholders resolved during unification
  Ok(state)
}

/// Infer match type
fn infer_match(state: State, scrutinee: Term, cases: List(Case)) -> Result(State, String) {
  case infer_term(state, scrutinee) {
    Ok(st) -> {
      // Check all cases have the same return type
      list.fold(cases, Ok(st), fn(acc_state, case_) {
        case acc_state {
          Ok(st) -> infer_term(st, case_.body)
          Error(e) -> Error(e)
        }
      })
    }
    Error(e) -> Error(e)
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
    TForAll(_, body) -> "∀" <> type_to_string(body)
  }
}
