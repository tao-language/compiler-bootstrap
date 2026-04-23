// Core evaluation - Normalization by Evaluation (NBE)
// Normalizes terms to values by evaluation.
// Values use De Bruijn levels (Var(0) = innermost binder).

import core/ast
import core/state
import gleam/list
import gleam/int

/// Evaluate a term to a value
pub fn eval(state: state.State, term: ast.Term) -> Result(ast.Value, String) {
  eval_term(state, term)
}

/// Evaluate a term to a value
fn eval_term(state: state.State, term: ast.Term) -> Result(ast.Value, String) {
  case term {
    ast.Var(name, idx) -> eval_var(state, idx)
    ast.Lam(name, _, body) -> {
      // Lambda is already a value - wrap in Closure
      let value = ast.Closure(name, body, [])
      Ok(value)
    }
    ast.App(lhs, rhs) -> {
      let fun_val = eval_term(state, lhs)
      let arg_val = eval_term(state, rhs)
      case fun_val {
        Ok(ast.Closure(_, body, _)) -> eval_term(state, body)
        Ok(fun) -> eval_app(state, fun, arg_val)
        Error(e) -> Error(e)
      }
    }
    ast.IntLit(n) -> Ok(ast.IntVal(n))
    ast.FloatLit(n) -> Ok(ast.FloatVal(n))
    ast.StringLit(s) -> Ok(ast.StringVal(s))
    ast.PatternVar(_) -> Error("Pattern variable in term")
    ast.PatternConstr(_, _) -> Error("Constructor in term")
    ast.Match(scrutinee, cases) -> eval_match(state, scrutinee, cases)
  }
}

/// Evaluate a variable reference
fn eval_var(state: state.State, idx: Int) -> Result(ast.Value, String) {
  case env_to_list(state), idx {
    [val], 0 -> Ok(val)
    [_, ..rest], n -> eval_var(state, n - 1)
    _, _ -> Error("Variable not found: " <> int.to_string(idx))
  }
}

/// Evaluate application
fn eval_app(state: state.State, fun: ast.Value, arg: Result(ast.Value, String)) -> Result(ast.Value, String) {
  case arg {
    Ok(arg_val) -> case fun {
      ast.Closure(_, body, _) -> eval_term(state, body)
      _ -> Error("Not a function")
    }
    Error(e) -> Error(e)
  }
}

/// Evaluate a match expression
fn eval_match(state: state.State, scrutinee: ast.Term, cases: List(ast.MatchCase)) -> Result(ast.Value, String) {
  case eval_term(state, scrutinee) {
    Ok(value) -> eval_match_value(state, value, cases)
    Error(e) -> Error(e)
  }
}

/// Evaluate match with a value
fn eval_match_value(state: state.State, value: ast.Value, cases: List(ast.MatchCase)) -> Result(ast.Value, String) {
  case cases {
    [] -> Error("No matching case")
    [first, ..rest] -> {
      case match_value(value, first.pattern) {
        Ok(result) -> Ok(result)
        Error(_) -> eval_match_value(state, value, rest)
      }
    }
  }
}

/// Match a value against a pattern
fn match_value(value: ast.Value, pattern: ast.Pattern) -> Result(ast.Value, String) {
  case value, pattern {
    ast.IntVal(n), ast.PatLit(ast.LInt(m)) if n == m -> Ok(value)
    ast.FloatVal(n), ast.PatLit(ast.LFloat(m)) if n == m -> Ok(value)
    ast.StringVal(s), ast.PatLit(ast.LString(m)) if s == m -> Ok(value)
    _, _ -> Error("Pattern mismatch")
  }
}

/// Convert environment to list
fn env_to_list(state: state.State) -> List(ast.Value) {
  // This is a simplified version - in practice, we'd need proper De Bruijn level management
  []
}

/// Evaluate a list of values
pub fn eval_list(state: state.State, values: List(ast.Value)) -> Result(List(ast.Value), String) {
  case values {
    [] -> Ok([])
    [v] ->
      case v {
        ast.Closure(_, body, _) -> {
          let new_state = state.State(..state)
          case eval_term(new_state, body) {
            Ok(val) -> Ok([val])
            Error(e) -> Error(e)
          }
        }
        _ -> Ok([v])
      }
    _ -> Error("Not a single value")
  }
}
