import core/syntax.{parse}
import core/ast.{term_to_string, Var, Lam}
import gleam/io
import gleam/list

pub fn main() {
  // Test: Just x
  let #(tx, ex) = parse("x")
  case ex {
    [] -> io.println("x parses to: " <> term_to_string(tx))
    [_, ..] -> io.println("x has " <> int.to_string(list.length(ex)) <> " errors")
  }
  
  // Test: $fn(x: $Int) => x
  let #(tl, el) = parse("$fn(x: $Int) => x")
  case el {
    [] -> {
      case tl {
        Lam([], #("x", _), body, _) -> {
          case body {
            Var(0, _) -> io.println("$fn(x: $Int) => x parses to Lam(Var(0))")
            _ -> io.println("$fn(x: $Int) => x body: " <> term_to_string(body))
          }
        }
        _ -> io.println("$fn(x: $Int) => x: not a Lam")
      }
    }
    [_, ..] -> io.println("$fn(x: $Int) => x has " <> int.to_string(list.length(el)) <> " errors")
  }
}

import gleam/int
import gleam/string
