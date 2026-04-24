// Tao Compiler - Multi-file compilation pipeline
// Compiles Tao source code to Core terms and evaluates them.

import core/ast.{type Term, type Value, type Type, Lit, LInt, IntVal, TVar}
import tao/ast.{type Module, type Stmt, Let, Fn, Expr as ExprStmt} as tao
import tao/desugar
import gleam/list
import core/eval

/// Compile a Tao module to a Core term and evaluate it
pub fn compile_module(module: Module) -> Result(#(Term, Value), List(String)) {
  case compile_stmts(module.statements, []) {
    Ok(#(term, value)) -> Ok(#(term, value))
    Error(errors) -> Error(errors)
  }
}

/// Compile a list of statements
fn compile_stmts(stmts: List(Stmt), env: List(#(String, Type))) -> Result(#(Term, Value), List(String)) {
  case stmts {
    [] -> Ok(#(Lit(LInt(0)), IntVal(0)))
    [first, ..rest] -> {
      case compile_stmt(first, env) {
        Ok(#(new_env, result)) -> compile_stmts(rest, new_env)
        Error(errors) -> Error(errors)
      }
    }
  }
}

/// Compile a single statement
fn compile_stmt(stmt: Stmt, env: List(#(String, Type))) -> Result(#(List(#(String, Type)), #(Term, Value)), List(String)) {
  case stmt {
    Let(name, value, _) -> {
      case compile_expr(value, env) {
        Ok(#(term, value)) -> {
          let new_env = list.append(env, [ #(name, TVar(0)) ])
          Ok(#(new_env, #(term, value)))
        }
        Error(errors) -> Error(errors)
      }
    }
    Fn(name, _params, body, _) -> {
      case compile_expr(body, env) {
        Ok(#(term, value)) -> {
          let new_env = list.append(env, [ #(name, TVar(1)) ])
          Ok(#(new_env, #(term, value)))
        }
        Error(errors) -> Error(errors)
      }
    }
    ExprStmt(expr, _) -> {
      case compile_expr(expr, env) {
        Ok(#(_term, _value)) -> Ok(#(env, #(Lit(LInt(0)), IntVal(0))))
        Error(errors) -> Error(errors)
      }
    }
    _ -> Ok(#(env, #(Lit(LInt(0)), IntVal(0))))
  }
}

/// Compile an expression to a Core term and value
fn compile_expr(expr: Expr, env: List(#(String, Type))) -> Result(#(Term, Value), List(String)) {
  case desugar.desugar_expr(expr, env) {
    Ok(#(term, _new_env)) -> {
      case eval.eval([], term) {
        Ok(value) -> Ok(#(term, value))
        Error(e) -> Error([e])
      }
    }
    Error(e) -> Error([e])
  }
}
