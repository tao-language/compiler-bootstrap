// Tao Desugarer - Expr -> Core Term conversion
// Converts high-level Tao expressions to core terms with De Bruijn indices.

import tao/ast as tao
import core/ast.{type Term, type Type, type Pattern, type Literal, PatVar, PatLit, PatConstr, PatternConstr, Match, MatchCase, Var, Lam, App, IntLit, FloatLit, StringLit, TVar, LInt, LFloat, LString}
import gleam/list

// ============================================================================
// TAo to CoRE DESUGARING
// ============================================================================

/// Desugar a Tao expression to a Core term
pub fn desugar_expr(expr: tao.Expr, env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case expr {
    tao.Var(name, _) -> Ok(#(Var(name, 0), env))
    tao.Lit(lit, _) -> Ok(#(term_from_literal(lit), env))
    tao.Lambda(params, body, _) -> desugar_lambda(params, body, env)
    tao.Call(fun, args, _) -> desugar_call(fun, args, env)
    tao.BinOp(left, op, right, _) -> desugar_binop(left, op, right, env)
    tao.Ctr(name, args, _) -> desugar_ctr(name, args, env)
    tao.Match(arg, cases, _) -> desugar_match(arg, cases, env)
    tao.If(cond, then_, else_, _) -> desugar_if(cond, then_, else_, env)
    tao.Ann(term, typ, _) -> desugar_ann(term, typ, env)
    tao.Hole(_) -> Ok(#(Var("??", -1), env))
    tao.Record(fields, _) -> desugar_record(fields, env)
    tao.Dot(record, field, _) -> desugar_dot(record, field, env)
  }
}

/// Desugar a Tao statement to a Core term
pub fn desugar_stmt(stmt: tao.Stmt, env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case stmt {
    tao.Let(name, value, _) -> {
      case desugar_expr(value, env) {
        Ok(#(val, new_env)) -> {
          let new_env2 = list.append(new_env, [ #(name, TVar(0)) ])
          Ok(#(val, new_env2))
        }
        Error(e) -> Error(e)
      }
    }
    tao.Fn(name, params, body, _) -> {
      case desugar_lambda(params, body, env) {
        Ok(#(lam, new_env)) -> {
          let new_env2 = list.append(new_env, [ #(name, TVar(1)) ])
          Ok(#(lam, new_env2))
        }
        Error(e) -> Error(e)
      }
    }
    tao.Expr(expr, _) -> desugar_expr(expr, env)
    _ -> Error("Unsupported statement")
  }
}

/// Convert a Tao literal to a Core term
fn term_from_literal(lit: tao.Literal) -> Term {
  case lit {
    tao.IntLit(n) -> IntLit(n)
    tao.FloatLit(n) -> FloatLit(n)
    tao.StringLit(s) -> StringLit(s)
  }
}

/// Desugar a lambda
fn desugar_lambda(params: List(tao.Param), body: tao.Expr, env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  // Simplified: assume single parameter
  case params {
    [param] -> {
      let param_env = list.append(env, [ #(param.name, TVar(0)) ])
      case desugar_expr(body, param_env) {
        Ok(#(body_term, _)) -> {
          let result = Ok(#(Lam(param.name, TVar(0), body_term), env))
          result
        }
        Error(e) -> Error(e)
      }
    }
    _ -> Error("Only single-parameter lambdas supported in prototype")
  }
}

/// Desugar a call
fn desugar_call(fun: tao.Expr, args: List(tao.Expr), env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(fun, env) {
    Ok(#(fun_term, new_env)) -> {
      case list.map(args, fn(arg) {
        case desugar_expr(arg, new_env) {
          Ok(#(arg_term, _)) -> arg_term
          Error(e) -> panic as e
        }
      }) {
        [arg] -> Ok(#(App(fun_term, arg), new_env))
        _ -> Error("Only single-argument calls supported in prototype")
      }
    }
    Error(e) -> Error(e)
  }
}

/// Desugar a binary operation
fn desugar_binop(left: tao.Expr, op: tao.BinOp, right: tao.Expr, env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(left, env) {
    Ok(#(left_term, new_env)) ->
      case desugar_expr(right, new_env) {
        Ok(#(right_term, final_env)) -> {
          let func_name = binop_to_func_name(op)
          Ok(#(App(Var(func_name, 0), App(Var(func_name, 0), right_term)), final_env))
        }
        Error(e) -> Error(e)
      }
    Error(e) -> Error(e)
  }
}

/// Convert a binary operator to a function name
fn binop_to_func_name(op: tao.BinOp) -> String {
  case op {
    tao.Add -> "+"
    tao.Sub -> "-"
    tao.Mul -> "*"
    tao.Div -> "/"
    tao.Eq -> "=="
    tao.Neq -> "!="
    tao.Lt -> "<"
    tao.Gt -> ">"
    tao.Le -> "<="
    tao.Ge -> ">="
    tao.And -> "and"
    tao.Or -> "or"
  }
}

/// Desugar a constructor
fn desugar_ctr(name: String, args: List(tao.Expr), env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case list.map(args, fn(arg) {
    case desugar_expr(arg, env) {
      Ok(#(arg_term, _)) -> arg_term
      Error(e) -> panic as e
    }
  }) {
    _ -> Ok(#(PatternConstr(name, []), env))
  }
}

/// Desugar a match expression
fn desugar_match(arg: tao.Expr, cases: List(tao.MatchClause), env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(arg, env) {
    Ok(#(arg_term, new_env)) -> {
      // Simplified: just return a placeholder match case
      Ok(#(Match(arg_term, [MatchCase(pattern: PatVar("_"), body: IntLit(0))]), new_env))
    }
    Error(e) -> Error(e)
  }
}

/// Convert a Tao pattern to a Core pattern
fn pat_to_pattern(pat: tao.Pattern) -> Pattern {
  case pat {
    tao.PatVar(name, _) -> PatVar(name)
    tao.PatLit(lit, _) -> PatLit(LInt(0))
    tao.PatConstr(name, patterns, _) -> {
      let inner_pats = list.map(patterns, pat_to_pattern)
      PatConstr(name, inner_pats)
    }
    tao.PatDot(record, field, _) -> PatVar(field)
  }
}

/// Desugar an if expression
fn desugar_if(cond: tao.Expr, then_: tao.Expr, else_: tao.Expr, env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(cond, env) {
    Ok(#(cond_term, new_env)) -> {
      case desugar_expr(then_, new_env) {
        Ok(#(then_term, env2)) ->
          case desugar_expr(else_, env2) {
            Ok(#(else_term, final_env)) -> {
              // If is desugared to a match on True/False
              Ok(#(Match(cond_term, [
                MatchCase(pattern: PatVar("true"), body: then_term),
                MatchCase(pattern: PatVar("false"), body: else_term),
              ]), final_env))
            }
            Error(e) -> Error(e)
          }
        Error(e) -> Error(e)
      }
    }
    Error(e) -> Error(e)
  }
}

/// Desugar a type annotation
fn desugar_ann(term: tao.Expr, typ: tao.TypeAst, env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(term, env) {
    Ok(#(term_term, new_env)) -> Ok(#(term_term, new_env))
    Error(e) -> Error(e)
  }
}

/// Desugar a record
fn desugar_record(fields: List(#(String, tao.Expr)), env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case list.map(fields, fn(f) {
    case desugar_expr(f.1, env) {
      Ok(#(term, _)) -> #(f.0, term)
      Error(e) -> panic as e
    }
  }) {
    _ -> Ok(#(PatternConstr("record", []), env))
  }
}

/// Desugar a field access
fn desugar_dot(record: tao.Expr, field: String, env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(record, env) {
    Ok(#(record_term, new_env)) -> Ok(#(PatternConstr(field, []), new_env))
    Error(e) -> Error(e)
  }
}
