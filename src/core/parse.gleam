import core/ast.{type AST}
import core/literals as lit
import gleam/option.{None, Some}
import gleam/result
import nibble.{do, return}
import nibble/lexer.{type Lexer, type Matcher}

type Token {
  Type
  Int(Int)
  Num(Float)
  LParen
  RParen
}

pub fn parse(source: String) -> Result(AST, String) {
  todo
}

fn lexer() -> Lexer(Token, Nil) {
  lexer.simple([
    lexer.keyword("%Type", "\\b", Type),
    lexer.int(Int),
    lexer.float(Num),
    lexer.token("(", LParen),
    lexer.token(")", RParen),
  ])
}

fn term() {
  todo
}
