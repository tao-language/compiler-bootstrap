// Tao Compiler - Multi-file compilation pipeline
// Compiles Tao source code to Core terms and evaluates them.

import core/ast as core_ast
import tao/ast as tao_ast
import tao/desugar
import gleam/list
import core/eval as core_eval

/// Compile a Tao module to a Core term and evaluate it
pub fn compile_module(module: tao_ast.Module) -> Result(#(core_ast.Term, core_ast.Value), List(String)) {
  case compile_stmts(module.statements, []) {
    Ok(#(term, value)) -> Ok(#(term, value))
    Error(errors) -> Error(errors)
  }
}

/// Compile a list of statements
fn compile_stmts(stmts: List(tao_ast.Stmt), env: List(#(String, core_ast.Type))) -> Result(#(core_ast.Term, core_ast.Value), List(String)) {
  case stmts {
    [] -> Ok(#(core_ast.Lit(core_ast.LInt(0)), core_ast.IntVal(0)))
    [first, ..rest] -> {
      case compile_stmt(first, env) {
        Ok(#(_new_env, _result)) -> compile_stmts(rest, env)
        Error(errors) -> Error(errors)
      }
    }
  }
}

/// Compile a single statement
fn compile_stmt(stmt: tao_ast.Stmt, env: List(#(String, core_ast.Type))) -> Result(#(List(#(String, core_ast.Type)), #(core_ast.Term, core_ast.Value)), List(String)) {
  case stmt {
    tao_ast.Let(name, value, _) -> {
      case compile_expr(value, env) {
        Ok(#(term, value)) -> {
          let new_env = list.append(env, [ #(name, core_ast.TVar(0)) ])
          Ok(#(new_env, #(term, value)))
        }
        Error(errors) -> Error(errors)
      }
    }
    tao_ast.Fn(name, _params, body, _) -> {
      case compile_expr(body, env) {
        Ok(#(term, value)) -> {
          let new_env = list.append(env, [ #(name, core_ast.TVar(1)) ])
          Ok(#(new_env, #(term, value)))
        }
        Error(errors) -> Error(errors)
      }
    }
    tao_ast.Expr(expr, _) -> {
      case compile_expr(expr, env) {
        Ok(#(_term, _value)) -> Ok(#(env, #(core_ast.Lit(core_ast.LInt(0)), core_ast.IntVal(0))))
        Error(errors) -> Error(errors)
      }
    }
    _ -> Ok(#(env, #(core_ast.Lit(core_ast.LInt(0)), core_ast.IntVal(0))))
  }
}

/// Compile an expression to a Core term and value
fn compile_expr(expr: tao_ast.Expr, env: List(#(String, core_ast.Type))) -> Result(#(core_ast.Term, core_ast.Value), List(String)) {
  case desugar.desugar_expr(expr, env) {
    Ok(#(term, _new_env)) -> {
      case core_eval.eval([], term) {
        Ok(value) -> Ok(#(term, value))
        Error(e) -> Error([e])
      }
    }
    Error(e) -> Error([e])
  }
}
