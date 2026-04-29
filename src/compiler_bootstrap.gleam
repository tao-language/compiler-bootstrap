import syntax/base_lexer as lexer
import syntax/base_lexer.{type Token}
import gleam/io
import gleam/list
import gleam/int

pub fn main() {
  // Check tokens for {x: 1, y: _}
  let tokens = lexer.tokenize("{x: 1, y: _}")
  io.println("Tokens for '{x: 1, y: _}':")
  let print_tok = fn(t: Token, i: Int) {
    io.println("  pos " <> int.to_string(i) <> ": '" <> t.value <> "' (" <> t.kind <> ")")
  }
  list.index_map(tokens, print_tok)
}
