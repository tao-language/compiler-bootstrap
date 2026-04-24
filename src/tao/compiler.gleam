// Tao Compiler - Multi-file compilation pipeline
// Compiles Tao source code to Core terms.

import core/state.{type State, new_state, type FfiEntry, Env}
import core/ast.{type Term, type Value, Var, Lam, App, Lit, Ctr, Match, Hole, Err, IntVal, FloatVal, StringVal, Closure, CtrVal, LitVal, HoleVal, ErrVal, LInt, LFloat, LString}
import tao/ast.{type Module, type Stmt, type Expr, Let, Fn, Expr as ExprStmt} as tao
import tao/desugar
import core/eval as eval

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
    [] -> Ok(#(Lit(LInt(0)), IntVal(0)))
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
          let new_state = state.State(
            env: state.State(..state).env,
            errors: state.State(..state).errors,
            hole_bindings: state.State(..state).hole_bindings,
          )
          Ok(new_state)
        }
        Error(errors) -> Error(errors)
      }
    }
    Fn(name, _params, body, _) -> {
      let new_state = state.State(
        env: state.State(..state).env,
        errors: state.State(..state).errors,
        hole_bindings: state.State(..state).hole_bindings,
      )
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
    Ok(#(term, new_env)) -> {
      let new_env2 = Env(
        bindings: new_env,
        ffi: state.env.ffi,
      )
      let new_state = state.State(
        env: new_env2,
        errors: state.State(..state).errors,
        hole_bindings: state.State(..state).hole_bindings,
      )
      case eval.eval(new_state, term) {
        Ok(value) -> Ok(#(term, value))
        Error(e) -> Error([e])
      }
    }
    Error(e) -> Error([e])
  }
}
