// Tao Desugarer - Expr -> Core Term conversion
// Converts high-level Tao expressions to core terms with De Bruijn indices.

import tao/ast as tao
import core/ast.{type Term, type Type, type Pattern, type Literal, PatVar, PatConstr, Lit, Ctr, Match, Var, Lam, App, Hole, Err, LInt, LFloat, LString, Case, TVar}
import gleam/list

// =============================================================================
// TAO TO CORE DESUGARING
// =============================================================================

/// Desugar a Tao expression to a Core term
pub fn desugar_expr(expr: tao.Expr, env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case expr {
    tao.Var(name, _) -> case env_index(env, name, 0) {
      Ok(idx) -> Ok(#(Var(name: name, index: idx), env))
      Error(e) -> Error(e)
    }
    tao.Lit(lit, _) -> Ok(#(term_from_literal(lit), env))
    tao.Lambda(params, body, _) -> desugar_lambda(params, body, env)
    tao.Call(fun, args, _) -> desugar_call(fun, args, env)
    tao.BinOp(left, op, right, _) -> desugar_binop(left, op, right, env)
    tao.Ctr(name, args, _) -> desugar_ctr(name, args, env)
    tao.Match(arg, cases, _) -> desugar_match(arg, cases, env)
    tao.If(cond, then_, else_, _) -> desugar_if(cond, then_, else_, env)
    tao.Ann(term, typ, _) -> desugar_ann(term, typ, env)
    tao.Hole(_) -> Ok(#(Hole(id: -1), env))
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
    tao.IntLit(n) -> Lit(LInt(n))
    tao.FloatLit(n) -> Lit(LFloat(n))
    tao.StringLit(s) -> Lit(LString(s))
  }
}

/// Find the index of a variable in the environment (De Bruijn index)
fn env_index(env: List(#(String, Type)), name: String, acc: Int) -> Result(Int, String) {
  case env {
    [] -> Error("Unknown variable: " <> name)
    [ #(n, _), ..rest ] ->
      case n == name {
        True -> Ok(acc)
        False -> env_index(rest, name, acc + 1)
      }
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
          let result = Ok(#(Lam(param: param.name, body: body_term), env))
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
      case list.try_map(args, fn(arg) {
        case desugar_expr(arg, new_env) {
          Ok(#(arg_term, _)) -> Ok(arg_term)
          Error(e) -> Error(e)
        }
      }) {
        Ok([arg]) -> Ok(#(App(fun: fun_term, arg: arg), new_env))
        Ok(_) -> Error("Only single-argument calls supported in prototype")
        Error(e) -> Error(e)
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
          Ok(#(App(
            fun: Var(name: func_name, index: 0),
            arg: App(
              fun: Var(name: func_name, index: 0),
              arg: right_term,
            ),
          ), final_env))
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
  case list.try_map(args, fn(arg) {
    case desugar_expr(arg, env) {
      Ok(#(arg_term, _)) -> Ok(arg_term)
      Error(e) -> Error(e)
    }
  }) {
    Ok(arg_terms) -> Ok(#(Ctr(tag: name, args: arg_terms), env))
    Error(e) -> Error(e)
  }
}

/// Desugar a match expression
fn desugar_match(arg: tao.Expr, cases: List(tao.MatchClause), env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(arg, env) {
    Ok(#(arg_term, new_env)) -> {
      // Simplified: just return a placeholder match case
      Ok(#(Match(scrutinee: arg_term, cases: [Case(pattern: PatVar(name: "_"), body: Lit(LInt(0)))]), new_env))
    }
    Error(e) -> Error(e)
  }
}

/// Convert a Tao pattern to a Core pattern
fn pat_to_pattern(pat: tao.Pattern) -> Pattern {
  case pat {
    tao.PatVar(name, _) -> PatVar(name)
    tao.PatLit(lit, _) -> PatConstr(tag: "lit", arg: PatVar(name: "lit"))
    tao.PatConstr(name, patterns, _) -> {
      case patterns {
        [] -> PatVar(name)
        [first] -> PatConstr(tag: name, arg: pat_to_pattern(first))
        _ -> {
          case list.last(patterns) {
            Ok(last) -> PatConstr(tag: name, arg: pat_to_pattern(last))
            Error(_) -> PatVar(name)
          }
        }
      }
    }
    tao.PatDot(record, field, _) -> PatVar(name: field)
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
              Ok(#(Match(
               scrutinee: cond_term,
                cases: [
                  Case(pattern: PatVar(name: "true"), body: then_term),
                  Case(pattern: PatVar(name: "false"), body: else_term),
                ],
              ), final_env))
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
  case list.try_map(fields, fn(f) {
    case desugar_expr(f.1, env) {
      Ok(#(term, _)) -> Ok(#(f.0, term))
      Error(e) -> Error(e)
    }
  }) {
    Ok(field_terms) -> Ok(#(Ctr(tag: "record", args: [Lit(LInt(0))]), env))
    Error(e) -> Error(e)
  }
}

/// Desugar a field access
fn desugar_dot(record: tao.Expr, field: String, env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(record, env) {
    Ok(#(_, new_env)) -> Ok(#(Var(name: field, index: 0), new_env))
    Error(e) -> Error(e)
  }
}
