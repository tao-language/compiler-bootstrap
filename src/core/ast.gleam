// Core language abstract syntax tree and runtime values.
// Uses De Bruijn indices for syntax (Term), De Bruijn levels for semantics (Value).

import gleam/list

// Type System

/// Core types
pub type Type {
  /// Type variable (holes for inference)
  TVar(Int)
  /// Function type: A -> B
  TPi(String, Type, Type)
  /// Universal quantification: ∀a. Type
  TForAll(String, Type)
}

/// Core terms (De Bruijn indices: Var(0) = closest binder above)
pub type Term {
  /// Variable reference
  Var(String, Int)
  /// Lambda abstraction: Lam(name, arg_type, body)
  Lam(String, Type, Term)
  /// Application
  App(Term, Term)
  /// Integer literal
  IntLit(Int)
  /// Float literal
  FloatLit(Float)
  /// String literal
  StringLit(String)
  /// Pattern variable (for pattern matching)
  PatternVar(String)
  /// Pattern constructor
  PatternConstr(String, List(Term))
  /// Pattern match
  Match(Term, List(MatchCase))
}

/// Match case for pattern matching
pub type MatchCase {
  MatchCase(pattern: Pattern, body: Term)
}

/// Patterns (for pattern matching in match expressions)
pub type Pattern {
  /// Variable pattern
  PatVar(String)
  /// Constructor pattern
  PatConstr(String, List(Pattern))
  /// Literal pattern
  PatLit(Literal)
}

/// Literals
pub type Literal {
  LInt(Int)
  LFloat(Float)
  LString(String)
}

/// Core values (evaluated results)
pub type Value {
  /// Closure: variable at level, body, and environment
  Closure(String, Term, List(Value))
  /// Integer value
  IntVal(Int)
  /// Float value
  FloatVal(Float)
  /// String value
  StringVal(String)
}

/// Get the free variables in a term (naive, not using set)
pub fn free_vars(term: Term) -> List(String) {
  case term {
    Var(name, _idx) -> [name]
    Lam(name, _, body) ->
      list.append(
        free_vars(body),
        case name {
          "" -> []
          _ -> [name]
        },
      )
    App(lhs, rhs) ->
      list.append(free_vars(lhs), free_vars(rhs))
    IntLit(_) -> []
    FloatLit(_) -> []
    StringLit(_) -> []
    PatternVar(_) -> []
    PatternConstr(_, args) -> list.fold(args, [], fn(acc, arg) { list.append(acc, free_vars(arg)) })
    Match(scrutinee, cases) -> {
      let rest = list.fold(cases, [], fn(acc, match_case) {
        list.append(acc, free_vars(match_case.body))
      })
      list.append(free_vars(scrutinee), rest)
    }
  }
}
