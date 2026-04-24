// Tao Compiler - Multi-file compilation pipeline
// Compiles Tao source code to Core terms.

import core/state.{type State, new_state, type FfiEntry, Env}
import core/ast.{type Term, type Value, type Type, Var, Lam, App, IntLit, FloatLit, StringLit, IntVal, FloatVal, StringVal, Closure, PatConstr, PatternConstr, PatternVar, Match, MatchCase, PatVar, TVar}
import tao/ast.{type Module, type Stmt, type Expr, Let, Fn, Expr as ExprStmt} as tao
import tao/desugar
import gleam/list

/// Compile a Tao module to a Core term
pub fn compile_module(module: Module, ffi: List(FfiEntry)) -> Result(#(Term, Value), List(String)) {
  let env = Env(
    bindings: [],
    ffi: ffi,
  )
  let state = new_state(env)
  
  case compile_stmts(module.statements, state) {
    Ok(#(term, value)) -> Ok(#(term, value))
    Error(errors) -> Error(errors)
  }
}

/// Compile a list of statements
fn compile_stmts(stmts: List(Stmt), state: State) -> Result(#(Term, Value), List(String)) {
  case stmts {
    [] -> Ok(#(IntLit(0), IntVal(0)))
    [first, ..rest] -> {
      case compile_stmt(first, state) {
        Ok(new_state) -> compile_stmts(rest, new_state)
        Error(errors) -> Error(errors)
      }
    }
  }
}

/// Compile a single statement
fn compile_stmt(stmt: Stmt, state: State) -> Result(State, List(String)) {
  case stmt {
    Let(name, value, _) -> {
      case compile_expr(value, state) {
        Ok(#(_term, _value)) -> {
          let new_state = state.push_binding(state, name, TVar(0))
          Ok(new_state)
        }
        Error(errors) -> Error(errors)
      }
    }
    Fn(name, _params, body, _) -> {
      let new_state = state.push_binding(state, name, TVar(1))
      Ok(new_state)
    }
    ExprStmt(expr, _) -> {
      case compile_expr(expr, state) {
        Ok(#(_term, _value)) -> Ok(state)
        Error(errors) -> Error(errors)
      }
    }
    _ -> Ok(state)
  }
}

/// Compile an expression to a Core term and value
fn compile_expr(expr: Expr, state: State) -> Result(#(Term, Value), List(String)) {
  case desugar.desugar_expr(expr, state.env.bindings) {
    Ok(#(term, _new_env)) -> {
      let value = eval_term(term)
      Ok(#(term, value))
    }
    Error(e) -> Error([e])
  }
}

/// Evaluate a Core term to a Value (simplified prototype version)
fn eval_term(term: Term) -> Value {
  case term {
    Var(_name, _idx) -> IntVal(0)
    IntLit(n) -> IntVal(n)
    FloatLit(n) -> FloatVal(n)
    StringLit(s) -> StringVal(s)
    Lam(_name, _typ, _body) -> Closure("x", term, [])
    App(_fun, _arg) -> IntVal(0)
    PatternConstr(_name, _args) -> IntVal(0)
    PatternVar(_name) -> IntVal(0)
    PatternConstr(_name, _args) -> IntVal(0)
    Match(_arg, _cases) -> IntVal(0)
  }
}
