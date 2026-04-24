// Tests for the Tao desugarer
import core/ast.{Var, Lit, LInt, Lam, App, Match, Case, TVar}
import tao/ast as tao
import tao/desugar
import syntax/span
import gleam/option.{type Option, None}

pub fn test_desugar_var() {
  let env = [#("x", TVar(0))]
  let expr = tao.Var("x", span.dummy())
  case desugar.desugar_expr(expr, env) {
    Ok(#(term, _)) -> case term {
      Var(name, index) -> {
        assert name == "x"
        assert index == 1
        True
      }
      _ -> panic as "Expected Var"
    }
    Error(e) -> panic as e
  }
}

pub fn test_desugar_var_basic() {
  let env = []
  let expr = tao.Var("x", span.dummy())
  case desugar.desugar_expr(expr, env) {
    Ok(_) -> panic as "Expected error"
    Error(e) -> {
      assert e == "Unknown variable: x"
      True
    }
  }
}

pub fn test_desugar_var_unknown() {
  let env = []
  let expr = tao.Var("unknown", span.dummy())
  case desugar.desugar_expr(expr, env) {
    Ok(_) -> panic as "Expected error"
    Error(e) -> {
      assert e == "Unknown variable: unknown"
      True
    }
  }
}

pub fn test_desugar_lit_int() {
  let expr = tao.Lit(tao.IntLit(42), span.dummy())
  case desugar.desugar_expr(expr, []) {
    Ok(#(term, _)) -> case term {
      Lit(LInt(42)) -> True
      _ -> panic as "Expected Lit(LInt(42))"
    }
    Error(e) -> panic as e
  }
}

pub fn test_desugar_lambda() {
  let env = []
  let param = tao.Param(name: "x", type_: None, span: span.dummy())
  let body = tao.Var("x", span.dummy())
  let expr = tao.Lambda([param], body, span.dummy())
  case desugar.desugar_expr(expr, env) {
    Ok(#(term, _)) -> case term {
      Lam(param, body) -> case body {
        Var(name, index) -> {
          assert name == "x"
          assert index == 0
          True
        }
        _ -> panic as "Expected Var in body"
      }
      _ -> panic as "Expected Lam"
    }
    Error(e) -> panic as e
  }
}

pub fn test_desugar_call() {
  let env = [#("add", TVar(0))]
  let fun = tao.Var("add", span.dummy())
  let arg = tao.Lit(tao.IntLit(1), span.dummy())
  let expr = tao.Call(fun, [arg], span.dummy())
  case desugar.desugar_expr(expr, env) {
    Ok(#(term, _)) -> case term {
      App(fun, arg) -> case fun {
        Var(name, index) -> {
          assert name == "add"
          assert index == 0
          True
        }
        _ -> panic as "Expected Var in fun"
      }
      _ -> panic as "Expected App"
    }
    Error(e) -> panic as e
  }
}

pub fn test_desugar_let() {
  let env = []
  let stmt = tao.Let("x", tao.Lit(tao.IntLit(1), span.dummy()), span.dummy())
  case desugar.desugar_stmt(stmt, env) {
    Ok(#(term, _)) -> case term {
      Lit(LInt(1)) -> True
      _ -> panic as "Expected Lit(LInt(1))"
    }
    Error(e) -> panic as e
  }
}

pub fn test_desugar_if() {
  let env = []
  let cond = tao.Var("true", span.dummy())
  let then_ = tao.Lit(tao.IntLit(1), span.dummy())
  let else_ = tao.Lit(tao.IntLit(2), span.dummy())
  let expr = tao.If(cond, then_, else_, span.dummy())
  case desugar.desugar_expr(expr, env) {
    Ok(#(term, _)) -> case term {
      Match(scrutinee, _cases) -> case scrutinee {
        Var(name, index) -> {
          assert name == "true"
          assert index == 0
          True
        }
        _ -> panic as "Expected Var in scrutinee"
      }
      _ -> panic as "Expected Match"
    }
    Error(e) -> panic as e
  }
}
