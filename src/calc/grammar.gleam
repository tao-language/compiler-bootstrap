// ============================================================================
// CALCULATOR - Simple Working Calculator Language
// ============================================================================
/// A simple calculator with +, *, and parentheses

import calc/ast.{type Expr, Add, Int, Mul}
import gleam/int
import gleam/result
import lexer
import parser.{type ParseResult, type Token}

pub type CalcParseResult(a) {
  CalcParseOk(ast: a, pos: Int)
  CalcParseError
}

pub fn parse(source: String) -> parser.ParseResult(Expr) {
  let tokens = lexer.tokenize(lexer.default_config(), "calc", source)

  case parse_expr(tokens, 0) {
    CalcParseOk(ast, _) -> parser.ParseResult(ast: ast, errors: [])
    CalcParseError -> parser.ParseResult(ast: panic as "Parse failed", errors: [])
  }
}

// expr -> term (('+' | '-') term)*
fn parse_expr(tokens: List(Token), pos: Int) -> CalcParseResult(Expr) {
  case parse_term(tokens, pos) {
    CalcParseOk(left, pos1) -> {
      parse_expr_rest(tokens, pos1, left)
    }
    CalcParseError -> CalcParseError
  }
}

fn parse_term(tokens: List(Token), pos: Int) -> CalcParseResult(Expr) {
  case parse_factor(tokens, pos) {
    CalcParseOk(left, pos1) -> {
      parse_term_rest(tokens, pos1, left)
    }
    CalcParseError -> CalcParseError
  }
}

fn parse_expr_rest(tokens: List(Token), pos: Int, left: Expr) -> CalcParseResult(Expr) {
  case get_token(tokens, pos) {
    Ok(token) -> {
      case token.kind, token.value {
        "Operator", "+" -> {
          case parse_term(tokens, pos + 1) {
            CalcParseOk(right, pos2) -> {
              parse_expr_rest(tokens, pos2, Add(left, right))
            }
            CalcParseError -> CalcParseOk(ast: left, pos: pos)
          }
        }
        _, _ -> CalcParseOk(ast: left, pos: pos)
      }
    }
    Error(_) -> CalcParseOk(ast: left, pos: pos)
  }
}

fn parse_term_rest(tokens: List(Token), pos: Int, left: Expr) -> CalcParseResult(Expr) {
  case get_token(tokens, pos) {
    Ok(token) -> {
      case token.kind, token.value {
        "Operator", "*" -> {
          case parse_factor(tokens, pos + 1) {
            CalcParseOk(right, pos2) -> {
              parse_term_rest(tokens, pos2, Mul(left, right))
            }
            CalcParseError -> CalcParseOk(ast: left, pos: pos)
          }
        }
        _, _ -> CalcParseOk(ast: left, pos: pos)
      }
    }
    Error(_) -> CalcParseOk(ast: left, pos: pos)
  }
}

// factor -> INT | '(' expr ')'
fn parse_factor(tokens: List(Token), pos: Int) -> CalcParseResult(Expr) {
  case get_token(tokens, pos) {
    Ok(token) -> {
      case token.kind {
        "Number" -> {
          CalcParseOk(ast: Int(int.parse(token.value) |> result.unwrap(0)), pos: pos + 1)
        }
        "LParen" -> {
          case parse_expr(tokens, pos + 1) {
            CalcParseOk(inner, pos2) -> {
              case get_token(tokens, pos2) {
                Ok(token2) if token2.kind == "RParen" -> {
                  CalcParseOk(ast: inner, pos: pos2 + 1)
                }
                _ -> CalcParseError
              }
            }
            CalcParseError -> CalcParseError
          }
        }
        _ -> CalcParseError
      }
    }
    Error(_) -> CalcParseError
  }
}

fn get_token(tokens: List(Token), pos: Int) -> Result(Token, Nil) {
  get_token_loop(tokens, pos, 0)
}

fn get_token_loop(tokens: List(Token), pos: Int, current: Int) -> Result(Token, Nil) {
  case tokens {
    [] -> Error(Nil)
    [token, ..rest] -> {
      case current == pos {
        True -> Ok(token)
        False -> get_token_loop(rest, pos, current + 1)
      }
    }
  }
}
