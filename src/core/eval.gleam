// Core evaluation - Normalization by Evaluation (NBE)
// Normalizes terms to values by evaluation.
// Values use De Bruijn levels (Var(0) = innermost binder).
//
// Terms use De Bruijn indices (Var(0) = closest binder above).
// Values use De Bruijn levels (Var(0) = innermost binder).
// The environment is a list of values where index 0 is the innermost binding.

import core/ast.{type Term, type Value, type Literal, type Case, type Pattern, Var, Lam, App, Lit, LInt, LFloat, LString, Ctr, Match, Hole, Err, PatLit, PatConstr, PatVar, PatAny, Closure, IntVal, FloatVal, StringVal, CtrVal, LitVal, HoleVal, ErrVal}
import gleam/list

/// Evaluate a term to a value with a De Bruijn level environment
pub fn eval(env: List(Value), term: Term) -> Result(Value, String) {
  eval_term(env, term)
}

/// Evaluate a term to a value
fn eval_term(env: List(Value), term: Term) -> Result(Value, String) {
  case term {
    Var(_, idx) -> eval_var(env, idx)
    Lam(param, body) -> {
      // Lambda is already a value - capture the current environment
      Ok(Closure(param: param, body: body, env: env))
    }
    App(fun, arg) -> {
      case eval_term(env, fun) {
        Ok(Closure(param: _, body: closure_body, env: closure_env)) -> {
          // Apply: evaluate arg in current env, then body in extended env
          case eval_term(env, arg) {
            Ok(arg_val) -> eval_term([arg_val, ..closure_env], closure_body)
            Error(e) -> Error(e)
          }
        }
        Ok(fun_val) -> {
          // Fun is a value but not a closure - need to apply it
          case eval_term(env, arg) {
            Ok(arg_val) -> eval_app(fun_val, arg_val)
            Error(e) -> Error(e)
          }
        }
        Error(e) -> Error(e)
      }
    }
    Lit(LInt(n)) -> Ok(IntVal(n))
    Lit(LFloat(n)) -> Ok(FloatVal(n))
    Lit(LString(s)) -> Ok(StringVal(s))
    Ctr(tag, args) -> case eval_ctr_args(env, args) {
      Ok(args_val) -> Ok(CtrVal(tag: tag, arg: args_val))
      Error(e) -> Error(e)
    }
    Match(scrutinee, cases) -> eval_match(env, scrutinee, cases)
    Hole(id) -> Ok(HoleVal(id: id))
    Err(message) -> Error(message)
  }
}

/// Evaluate constructor arguments
fn eval_ctr_args(env: List(Value), args: List(Term)) -> Result(Value, String) {
  case args {
    [] -> Ok(LitVal(LInt(0)))  // Empty constructor
    [arg] -> eval_term(env, arg)
    _ -> {
      // For multi-arg constructors, evaluate all and return last as value
      case list.try_map(args, fn(a) { eval_term(env, a) }) {
        Ok(vals) -> case list.last(vals) {
          Ok(last) -> Ok(last)
          Error(_) -> Ok(LitVal(LInt(0)))
        }
        Error(e) -> Error(e)
      }
    }
  }
}

/// Evaluate a variable reference (De Bruijn level)
/// Var(0) = innermost binding = env[0]
fn eval_var(env: List(Value), idx: Int) -> Result(Value, String) {
  case env_drop_to(env, idx) {
    [val] -> Ok(val)
    _ -> Error("Variable not found at level " <> int_to_string(idx))
  }
}

/// Drop the first n elements from the environment (converts De Bruijn level to index)
/// env_drop_to([v2, v1, v0], 0) = [v0]  (innermost binding)
/// env_drop_to([v2, v1, v0], 1) = [v1]  (next innermost)
fn env_drop_to(env: List(Value), idx: Int) -> List(Value) {
  case env, idx {
    _, 0 -> env
    [_, ..rest], _ if idx > 0 -> env_drop_to(rest, idx - 1)
    _, _ -> []
  }
}

/// Evaluate application of a non-lambda value
fn eval_app(fun_val: Value, _arg_val: Value) -> Result(Value, String) {
  case fun_val {
    Closure(_, _, _) -> Error("Should have been handled in eval_term")
    _ -> Error("Not a function: " <> value_to_string(fun_val))
  }
}

/// Evaluate a match expression
fn eval_match(env: List(Value), scrutinee: Term, cases: List(Case)) -> Result(Value, String) {
  case eval_term(env, scrutinee) {
    Ok(value) -> eval_match_value(value, cases)
    Error(e) -> Error(e)
  }
}

/// Evaluate match with a value
fn eval_match_value(value: Value, cases: List(Case)) -> Result(Value, String) {
  case cases {
    [] -> Error("No matching case")
    [first, ..rest] -> {
      case match_value(value, first.pattern) {
        Ok(result) -> Ok(result)
        Error(_) -> eval_match_value(value, rest)
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

/// Convert integer to string
fn int_to_string(n: Int) -> String {
  case n < 0 {
    True -> "-" <> int_to_string(-n)
    False -> case n {
      0 -> "0"
      _ -> int_to_string(n / 10) <> int_digit_to_char(n % 10)
    }
  }
}

fn int_digit_to_char(d: Int) -> String {
  case d {
    0 -> "0"
    1 -> "1"
    2 -> "2"
    3 -> "3"
    4 -> "4"
    5 -> "5"
    6 -> "6"
    7 -> "7"
    8 -> "8"
    9 -> "9"
    _ -> ""
  }
}

/// Convert value to string for debugging
fn value_to_string(val: Value) -> String {
  case val {
    Closure(param, _, _) -> "<lambda " <> param <> ">"
    IntVal(n) -> "Int(" <> int_to_string(n) <> ")"
    FloatVal(n) -> "Float(" <> float_to_string(n) <> ")"
    StringVal(s) -> "String(" <> s <> ")"
    CtrVal(tag, _) -> "Ctr(" <> tag <> ")"
    LitVal(lit) -> "Lit(" <> literal_to_string(lit) <> ")"
    HoleVal(id) -> "Hole(" <> int_to_string(id) <> ")"
    ErrVal -> "Err"
  }
}

fn float_to_string(f: Float) -> String {
  case f {
    _ -> "<float>"
  }
}

fn literal_to_string(lit: Literal) -> String {
  case lit {
    LInt(n) -> int_to_string(n)
    LFloat(n) -> float_to_string(n)
    LString(s) -> s
  }
}
