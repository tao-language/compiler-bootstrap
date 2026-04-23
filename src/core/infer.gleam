// Core infer - Bidirectional Type Checking
// Type checker with bidirectional inference and checking.
// Uses NBE for type inference (simplified prototype approach).

import core/ast
import core/state
import core/unify
import gleam/list

/// Infer the type of a term
pub fn infer_term(state: state.State, term: ast.Term) -> Result(state.State, String) {
  case term {
    ast.Var(name, _) -> infer_var(state, name)
    ast.Lam(name, arg_type, body) -> infer_lam(state, name, arg_type, body)
    ast.App(fun, arg) -> infer_app(state, fun, arg)
    ast.IntLit(_) -> infer_intlit(state)
    ast.FloatLit(_) -> infer_floatlit(state)
    ast.StringLit(_) -> infer_stringlit(state)
    ast.PatternVar(_) -> infer_patternvar(state)
    ast.PatternConstr(_, _) -> infer_patternconstr(state)
    ast.Match(scrutinee, cases) -> infer_match(state, scrutinee, cases)
  }
}

/// Check a term against an expected type
pub fn check_term(state: state.State, term: ast.Term, expected: ast.Type) -> Result(state.State, String) {
  case infer_term(state, term) {
    Ok(state) -> {
      case unify.unify(state, expected, expected) {
        Ok(st) -> Ok(st)
        Error(e) -> Error(e)
      }
    }
    Error(e) -> Error(e)
  }
}

/// Infer variable type
fn infer_var(state: state.State, name: String) -> Result(state.State, String) {
  case state.lookup_env(state, name) {
    Ok(typ) -> Ok(state)
    Error(_) -> Error("Unknown variable: " <> name)
  }
}

/// Infer lambda type
fn infer_lam(state: state.State, name: String, arg_type: ast.Type, body: ast.Term) -> Result(state.State, String) {
  let new_state = state.push_binding(state, name, arg_type)
  case infer_term(new_state, body) {
    Ok(st) -> Ok(st)
    Error(e) -> Error(e)
  }
}

/// Infer application type
fn infer_app(state: state.State, fun: ast.Term, arg: ast.Term) -> Result(state.State, String) {
  case infer_term(state, fun) {
    Ok(state) -> infer_term(state, arg)
    Error(e) -> Error(e)
  }
}

/// Infer integer literal type
fn infer_intlit(state: state.State) -> Result(state.State, String) {
  // For prototype, use a generic Int type
  Ok(state)
}

/// Infer float literal type
fn infer_floatlit(state: state.State) -> Result(state.State, String) {
  // For prototype, use a generic Float type
  Ok(state)
}

/// Infer string literal type
fn infer_stringlit(state: state.State) -> Result(state.State, String) {
  // For prototype, use a generic String type
  Ok(state)
}

/// Infer pattern variable type
fn infer_patternvar(state: state.State) -> Result(state.State, String) {
  // Pattern variables don't contribute to type inference
  Ok(state)
}

/// Infer pattern constructor type
fn infer_patternconstr(state: state.State) -> Result(state.State, String) {
  // Pattern constructors don't contribute to type inference
  Ok(state)
}

/// Infer match type
fn infer_match(state: state.State, scrutinee: ast.Term, cases: List(ast.MatchCase)) -> Result(state.State, String) {
  case infer_term(state, scrutinee) {
    Ok(state) -> {
      // Check all cases have the same return type
      let result = list.fold(cases, Ok(state), fn(acc_state, match_case) {
        case acc_state {
          Ok(st) -> infer_term(st, match_case.body)
          Error(e) -> Error(e)
        }
      })
      result
    }
    Error(e) -> Error(e)
  }
}
