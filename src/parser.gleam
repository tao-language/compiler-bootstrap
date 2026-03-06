// ============================================================================
// PARSER - Simple String Parser Combinators
// ============================================================================

/// A simple parser combinator library for parsing string tokens.
/// Produces parse trees that can be formatted by the formatter.
import gleam/list
import gleam/result
import gleam/string

// ============================================================================
// TYPES
// ============================================================================

/// A parse tree node
pub type ParseTree {
  /// A token leaf
  TreeToken(String)
  /// A named node with children
  TreeNode(name: String, children: List(ParseTree))
}

/// A parser that produces a parse tree
pub type Parser {
  Parser(run: fn(List(String)) -> Result(#(ParseTree, List(String)), String))
}

// ============================================================================
// BASIC PARSERS
// ============================================================================

/// Parse a specific token
pub fn token(value: String) -> Parser {
  Parser(fn(tokens) {
    case tokens {
      [] -> Error("Expected token: " <> value)
      [t, ..rest] if t == value -> Ok(#(TreeToken(value), rest))
      [t, ..] -> Error("Expected " <> value <> " but got " <> t)
    }
  })
}

/// Parse and capture any token as a named node
pub fn named(name: String) -> Parser {
  Parser(fn(tokens) {
    case tokens {
      [] -> Error("Expected " <> name)
      [t, ..rest] -> Ok(#(TreeNode(name, [TreeToken(t)]), rest))
    }
  })
}

/// Parse and capture any token
pub fn any_token() -> Parser {
  Parser(fn(tokens) {
    case tokens {
      [] -> Error("Expected token")
      [t, ..rest] -> Ok(#(TreeToken(t), rest))
    }
  })
}

// ============================================================================
// COMBINATORS
// ============================================================================

/// Sequence: parse p1 then p2, combine into tree node
pub fn seq2(p1: Parser, p2: Parser) -> Parser {
  Parser(fn(tokens) {
    use #(r1, tokens1) <- result.try(p1.run(tokens))
    use #(r2, tokens2) <- result.try(p2.run(tokens1))
    Ok(#(TreeNode("Seq", [r1, r2]), tokens2))
  })
}

/// Sequence three parsers
pub fn seq3(p1: Parser, p2: Parser, p3: Parser) -> Parser {
  Parser(fn(tokens) {
    use #(r1, tokens1) <- result.try(p1.run(tokens))
    use #(r2, tokens2) <- result.try(p2.run(tokens1))
    use #(r3, tokens3) <- result.try(p3.run(tokens2))
    Ok(#(TreeNode("Seq", [r1, r2, r3]), tokens3))
  })
}

/// Choice: try p1, if fails try p2
pub fn choice(p1: Parser, p2: Parser) -> Parser {
  Parser(fn(tokens) {
    case p1.run(tokens) {
      Ok(result) -> Ok(result)
      Error(_) -> p2.run(tokens)
    }
  })
}

/// Choice from list of parsers
pub fn choice_many(parsers: List(Parser)) -> Parser {
  Parser(fn(tokens) { choice_loop(parsers, tokens) })
}

fn choice_loop(
  parsers: List(Parser),
  tokens: List(String),
) -> Result(#(ParseTree, List(String)), String) {
  case parsers {
    [] -> Error("No alternatives matched")
    [p, ..rest] -> {
      case p.run(tokens) {
        Ok(result) -> Ok(result)
        Error(_) -> choice_loop(rest, tokens)
      }
    }
  }
}

/// Optional: parse or return empty token
pub fn opt(p: Parser) -> Parser {
  Parser(fn(tokens) {
    case p.run(tokens) {
      Ok(result) -> Ok(result)
      Error(_) -> Ok(#(TreeToken(""), tokens))
    }
  })
}

/// Zero or more repetitions
pub fn rep(p: Parser) -> Parser {
  Parser(fn(tokens) {
    use #(parts, remaining) <- result.try(rep_loop(p, tokens, []))
    Ok(#(TreeNode("Rep", parts), remaining))
  })
}

fn rep_loop(
  p: Parser,
  tokens: List(String),
  acc: List(ParseTree),
) -> Result(#(List(ParseTree), List(String)), String) {
  case p.run(tokens) {
    Ok(#(part, remaining)) -> rep_loop(p, remaining, [part, ..acc])
    Error(_) -> Ok(#(acc |> list.reverse, tokens))
  }
}

/// One or more repetitions
pub fn rep1(p: Parser) -> Parser {
  Parser(fn(tokens) {
    use #(first, remaining) <- result.try(p.run(tokens))
    use #(parts, remaining2) <- result.try(rep_loop(p, remaining, [first]))
    Ok(#(TreeNode("Rep1", parts), remaining2))
  })
}

/// Map parser result
pub fn map(p: Parser, f: fn(ParseTree) -> ParseTree) -> Parser {
  Parser(fn(tokens) {
    use #(result, tokens) <- result.try(p.run(tokens))
    Ok(#(f(result), tokens))
  })
}

// ============================================================================
// RUNNING PARSERS
// ============================================================================

/// Run a parser on a string input
pub fn parse_string(parser: Parser, input: String) -> Result(ParseTree, String) {
  let tokens = tokenize(input)
  case parser.run(tokens) {
    Ok(#(result, remaining)) ->
      case remaining {
        [] -> Ok(result)
        _ -> Error("Unexpected tokens: " <> string.join(remaining, " "))
      }
    Error(e) -> Error(e)
  }
}

/// Tokenize input string
fn tokenize(input: String) -> List(String) {
  input
  |> string.replace("(", " ( ")
  |> string.replace(")", " ) ")
  |> string.replace("{", " { ")
  |> string.replace("}", " } ")
  |> string.replace("=", " = ")
  |> string.replace("+", " + ")
  |> string.replace(",", " , ")
  |> string.split(" ")
  |> list.filter(fn(s) { s != "" })
}
