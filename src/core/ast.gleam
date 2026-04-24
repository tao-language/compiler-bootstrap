// Core language abstract syntax tree and runtime values.
// Uses De Bruijn indices for syntax (Term), De Bruijn levels for semantics (Value).

import gleam/list
import gleam/int

// =============================================================================
// CORE TYPES
// =============================================================================

/// Core types for type checking
pub type Type {
  TVar(id: Int)
  TPi(name: String, arg: Type, body: Type)
  TForAll(name: String, body: Type)
}

// =============================================================================
// CORE TERMS (De Bruijn indices: Var(0) = closest binder above)
// =============================================================================

/// Core terms (syntax)
pub type Term {
  Var(name: String, index: Int)
  Lam(param: String, body: Term)
  App(fun: Term, arg: Term)
  Lit(value: Literal)
  Ctr(tag: String, args: List(Term))
  Match(scrutinee: Term, cases: List(Case))
  Hole(id: Int)
  Err(message: String)
}

/// A case in a match expression
pub type Case {
  Case(pattern: Pattern, body: Term)
}

/// Patterns (for pattern matching in match expressions)
pub type Pattern {
  PatVar(name: String)
  PatConstr(tag: String, arg: Pattern)
  PatLit(value: Literal)
  PatAny
}

/// Literals
pub type Literal {
  LInt(value: Int)
  LFloat(value: Float)
  LString(value: String)
}

// =============================================================================
// CORE VALUES (De Bruijn levels: Var(0) = innermost binder)
// =============================================================================

/// Core values (evaluated results)
pub type Value {
  /// Closure: variable at level, body, and environment
  Closure(param: String, body: Term, env: List(Value))
  /// Integer value
  IntVal(value: Int)
  /// Float value
  FloatVal(value: Float)
  /// String value
  StringVal(value: String)
  /// Constructor value
  CtrVal(tag: String, arg: Value)
  /// Literal value (for matching)
  LitVal(value: Literal)
  /// Hole value (for type inference)
  HoleVal(id: Int)
  /// Error value
  ErrVal
}

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

/// Get the free variables in a term (naive, not using set)
pub fn free_vars(term: Term) -> List(String) {
  case term {
    Var(name, _) -> [name]
    Lam(param, body) ->
      list.append(
        free_vars(body),
        case param {
          "" -> []
          _ -> [param]
        },
      )
    App(fun, arg) ->
      list.append(free_vars(fun), free_vars(arg))
    Lit(_) -> []
    Ctr(_, args) -> list.fold(args, [], fn(acc, arg) { list.append(acc, free_vars(arg)) })
    Match(scrutinee, cases) ->
      list.fold(cases, free_vars(scrutinee), fn(acc, case_) {
        list.append(acc, free_vars(case_.body))
      })
    Hole(_) -> []
    Err(_) -> []
  }
}

/// Get the free variables in a type
pub fn free_vars_type(typ: Type) -> List(String) {
  case typ {
    TVar(id) ->
      case id < 0 {
        True -> ["??"]
        False -> ["a" <> int.to_string(id)]
      }
    TPi(name, arg, body) ->
      list.append(
        free_vars_type(arg),
        case name {
          "" -> free_vars_type(body)
          _ -> [name] |> list.append(free_vars_type(body))
        },
      )
    TForAll(name, body) ->
      case name {
        "" -> free_vars_type(body)
        _ -> free_vars_type(body)
      }
  }
}
