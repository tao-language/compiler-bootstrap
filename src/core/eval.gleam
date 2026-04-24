// Core evaluation - Normalization by Evaluation (NBE)
// Normalizes terms to values by evaluation.
// Values use De Bruijn levels (Var(0) = innermost binder).

import core/ast.{type Term, type Value, type Literal, type Case, type Pattern, Lit, LInt, LFloat, LString, PatLit, PatConstr, PatVar, PatAny, Closure, IntVal, FloatVal, StringVal, CtrVal, LitVal, HoleVal, ErrVal}
import core/state
import gleam/list
import gleam/int

/// Evaluate a term to a value
pub fn eval(state: state.State, term: Term) -> Result(Value, String) {
  eval_term(state, term)
}

/// Evaluate a term to a value
fn eval_term(state: state.State, term: Term) -> Result(Value, String) {
  case term {
    ast.Var(name, idx) -> eval_var(state, idx)
    ast.Lam(param, body) -> {
      // Lambda is already a value - wrap in Closure
      let value = Closure(param: param, body: body, env: [])
      Ok(value)
    }
    ast.App(fun, arg) -> {
      case eval_term(state, fun) {
        Ok(Closure(_, body, _)) -> eval_term(state, body)
        Ok(fun) -> {
          case eval_term(state, arg) {
            Ok(arg_val) -> eval_app(state, fun, arg_val)
            Error(e) -> Error(e)
          }
        }
        Error(e) -> Error(e)
      }
    }
    ast.Lit(LInt(n)) -> Ok(IntVal(n))
    ast.Lit(LFloat(n)) -> Ok(FloatVal(n))
    ast.Lit(LString(s)) -> Ok(StringVal(s))
    ast.Ctr(tag, args) -> {
      case eval_ctr_args(state, args) {
        Ok(args_val) -> Ok(CtrVal(tag: tag, arg: args_val))
        Error(e) -> Error(e)
      }
    }
    ast.Match(scrutinee, cases) -> eval_match(state, scrutinee, cases)
    ast.Hole(id) -> Ok(HoleVal(id: id))
    ast.Err(message) -> Error(message)
  }
}

/// Evaluate constructor arguments
fn eval_ctr_args(state: state.State, args: List(Term)) -> Result(Value, String) {
  case args {
    [] -> Ok(LitVal(LInt(0)))  // Empty constructor
    [arg] -> eval_term(state, arg)
    _ -> {
      // For multi-arg constructors, return the last argument as the value
      case list.last(args) {
        Ok(arg) -> eval_term(state, arg)
        Error(_) -> Ok(LitVal(LInt(0)))
      }
    }
  }
}

/// Evaluate a variable reference
fn eval_var(state: state.State, idx: Int) -> Result(Value, String) {
  case env_to_list(state), idx {
    [val], 0 -> Ok(val)
    [_, ..rest], n -> eval_var(state, n - 1)
    _, _ -> Error("Variable not found: " <> int.to_string(idx))
  }
}

/// Evaluate application
fn eval_app(state: state.State, fun: Value, arg_val: Value) -> Result(Value, String) {
  case fun {
    Closure(_, body, _) -> eval_term(state, body)
    _ -> Error("Not a function")
  }
}

/// Evaluate a match expression
fn eval_match(state: state.State, scrutinee: Term, cases: List(Case)) -> Result(Value, String) {
  case eval_term(state, scrutinee) {
    Ok(value) -> eval_match_value(state, value, cases)
    Error(e) -> Error(e)
  }
}

/// Evaluate match with a value
fn eval_match_value(state: state.State, value: Value, cases: List(Case)) -> Result(Value, String) {
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
fn match_value(value: Value, pattern: Pattern) -> Result(Value, String) {
  case value, pattern {
    IntVal(n), PatLit(LInt(m)) if n == m -> Ok(value)
    FloatVal(n), PatLit(LFloat(m)) if n == m -> Ok(value)
    StringVal(s), PatLit(LString(m)) if s == m -> Ok(value)
    CtrVal(tag, arg), PatConstr(name, inner) if tag == name -> {
      match_value(arg, inner)
    }
    _, PatVar(_) -> Ok(value)  // Bind name to value
    _, PatAny -> Ok(value)  // Match anything
    _, _ -> Error("Pattern mismatch")
  }
}

/// Match a literal value against a literal pattern
fn match_literal(value: Literal, pattern: Literal) -> Bool {
  case value, pattern {
    LInt(n), LInt(m) -> n == m
    LFloat(n), LFloat(m) -> n == m
    LString(s), LString(m) -> s == m
    _, _ -> False
  }
}

/// Convert environment to list
fn env_to_list(state: state.State) -> List(Value) {
  // This is a simplified version - in practice, we'd need proper De Bruijn level management
  []
}

/// Evaluate a list of values
pub fn eval_list(state: state.State, values: List(Value)) -> Result(List(Value), String) {
  case values {
    [] -> Ok([])
    [v] ->
      case v {
        Closure(_, body, _) -> {
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
