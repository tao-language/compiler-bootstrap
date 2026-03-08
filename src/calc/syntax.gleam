// ============================================================================
// CALCULATOR SYNTAX - Grammar Definition
// ============================================================================
/// Calculator language with +, *, and parentheses
/// 
/// Grammar:
///   expr  -> term (('+' | '-') term)*
///   term  -> factor (('*' | '/') factor)*
///   factor -> NUMBER | '(' expr ')'

import calc/ast.{type Expr, Add, Int, Mul}
import gleam/int
import gleam/list
import gleam/result
import grammar.{type Grammar, type ParseChild, ChildAST, ChildToken}
import parser.{ParseResult, type Token}

// ============================================================================
// GRAMMAR DEFINITION
// ============================================================================

pub fn calc_grammar() -> Grammar(Expr) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.with_token("Number")
  |> grammar.with_token("Operator")
  |> grammar.with_token("LParen")
  |> grammar.with_token("RParen")
  
  // expr -> term (('+'' | '-') term)*
  |> grammar.rule(
    "Expr",
    grammar.seq([
      grammar.ref("Term"),
      grammar.many(grammar.seq([
        grammar.choice([
          grammar.keyword("+"),
          grammar.keyword("-"),
        ]),
        grammar.ref("Expr"),
      ])),
    ]),
    fn(children) {
      case children {
        [ChildAST(left), ..ops] -> fold_ops(left, ops)
        _ -> panic as "Invalid Expr children"
      }
    },
    10,  // Precedence for + and -
  )

  // term -> factor (('*' | '/') factor)*
  |> grammar.rule(
    "Term",
    grammar.seq([
      grammar.ref("Factor"),
      grammar.many(grammar.seq([
        grammar.choice([
          grammar.keyword("*"),
          grammar.keyword("/"),
        ]),
        grammar.ref("Term"),
      ])),
    ]),
    fn(children) {
      case children {
        [ChildAST(left), ..ops] -> fold_ops(left, ops)
        _ -> panic as "Invalid Term children"
      }
    },
    20,  // Precedence for * and /
  )
  
  // factor -> NUMBER | '(' expr ')'
  |> grammar.rule(
    "Factor",
    grammar.choice([
      grammar.token("Number"),
      grammar.seq([
        grammar.token("LParen"),
        grammar.ref("Expr"),
        grammar.token("RParen"),
      ]),
    ]),
    fn(children) {
      case children {
        [ChildToken(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
        [_, ChildAST(expr), _] -> expr
        _ -> panic as "Invalid factor"
      }
    },
    30,  // Highest precedence for atoms
  )
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

fn fold_ops(left: Expr, ops: List(ParseChild(Expr))) -> Expr {
  // ops should be: [token, operand, token, operand, ...]
  // Build left-associative tree by processing pairs in order
  case ops {
    [] -> left
    [ChildToken(token), ChildAST(right), ..rest] -> {
      let new_left = case token.value {
        "+" -> Add(left, right)
        "-" -> panic as "Subtraction not implemented"
        "*" -> Mul(left, right)
        "/" -> panic as "Division not implemented"
        _ -> panic as "Unknown operator"
      }
      fold_ops(new_left, rest)
    }
    _ -> left
  }
}

// ============================================================================
// PUBLIC API
// ============================================================================

pub fn parse(source: String) -> parser.ParseResult(Expr) {
  grammar.parse(calc_grammar(), source)
}

pub fn format(ast: Expr) -> String {
  format_expr(ast, 0)
}

fn format_expr(expr: Expr, parent_prec: Int) -> String {
  case expr {
    Int(n) -> int.to_string(n)
    Add(l, r) -> {
      let prec = 10
      let s = format_expr(l, prec) <> " + " <> format_expr(r, prec + 1)
      case prec < parent_prec {
        True -> "(" <> s <> ")"
        False -> s
      }
    }
    Mul(l, r) -> {
      let prec = 20
      let s = format_expr(l, prec) <> " * " <> format_expr(r, prec + 1)
      case prec < parent_prec {
        True -> "(" <> s <> ")"
        False -> s
      }
    }
  }
}
