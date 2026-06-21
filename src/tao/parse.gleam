import gleam/int
import gleam/list
import gleam/option.{None, Some}
import gleam/result.{try}
import gleam/set
import gleam/string
import nibble.{type Parser, do, return}
import nibble/lexer.{type Lexer}
import nibble/pratt
import simplifile
import syntax/span.{type Span, Span}
import tao/ast.{type BinaryOp, type Expr, type Pattern, type Stmt, type UnaryOp} as tao
import tao/error.{type Error} as e

pub type Token {
  // Keywords
  KwImport
  KwAs
  KwFn
  KwLet
  KwMut
  KwMatch
  KwError

  // Values
  Name(String)
  IntLit(Int)
  FloatLit(Float)

  // Symbols
  LParen
  RParen
  LBrace
  RBrace
  LBracket
  RBracket
  LAngle
  RAngle
  Colon
  Semicolon
  Comma
  Dot
  Equals
  FatArrow
  ThinArrow
  Question
  Pipe
  At

  // Operators
  Add
  Sub
  Mul
  Div
}

pub fn lex(
  file: String,
  source: String,
) -> Result(List(lexer.Token(Token)), Error) {
  case lexer.run(source, lexer()) {
    Ok(tokens) -> Ok(tokens)
    Error(lexer.NoMatchFound(row, col, lexeme)) ->
      Error(e.UnexpectedToken(lexeme, Span(file, row, col, row, col)))
  }
}

pub fn expression(file: String, source: String) -> Result(Expr, Error) {
  use tokens <- try(lex(file, source))
  case nibble.run(tokens, expr(file)) {
    Ok(expr) -> Ok(expr)
    Error(err) -> {
      echo err
      todo
    }
  }
}

pub fn statements(file: String, source: String) -> Result(List(Stmt), Error) {
  use tokens <- try(lex(file, source))
  case nibble.run(tokens, nibble.many(stmt(file))) {
    Ok(stmts) -> Ok(stmts)
    Error(err) -> {
      echo err
      todo
    }
  }
}

fn lexer() -> Lexer(Token, Nil) {
  let reserved = ["import", "as", "fn", "let", "mut", "match", "error"]
  lexer.simple([
    // Keywords
    lexer.keyword("import", "\\W", KwImport),
    lexer.keyword("as", "\\W", KwAs),
    lexer.keyword("fn", "\\W", KwFn),
    lexer.keyword("let", "\\W", KwLet),
    lexer.keyword("match", "\\W", KwMatch),
    lexer.keyword("error", "\\W", KwError),

    // Names
    lexer.identifier("[_a-zA-Z]", "[_\\w]", set.from_list(reserved), Name),

    // Int and Float literals
    lexer.number(IntLit, FloatLit),

    // Single-line comments (// to end of line)
    lexer.comment("//", fn(_) { Nil }) |> lexer.ignore,

    // Two-character symbols (must come before single-char)
    lexer.token("=>", FatArrow),
    lexer.token("->", ThinArrow),
    lexer.token("<", LAngle),
    lexer.token(">", RAngle),

    // Single-character symbols
    lexer.token("(", LParen),
    lexer.token(")", RParen),
    lexer.token("{", LBrace),
    lexer.token("}", RBrace),
    lexer.token("[", LBracket),
    lexer.token("]", RBracket),
    lexer.token(":", Colon),
    lexer.token(";", Semicolon),
    lexer.token(",", Comma),
    lexer.token(".", Dot),
    lexer.symbol("=", "[^>]", Equals),
    lexer.token("?", Question),
    lexer.token("|", Pipe),
    lexer.token("@", At),

    // Whitespace
    lexer.whitespace(Nil) |> lexer.ignore,
  ])
}

fn stmt(file: String) -> Parser(Stmt, Token, Nil) {
  nibble.one_of([let_(file), test_(file)])
}

fn let_(file: String) -> Parser(Stmt, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(KwLet))
  use pat <- do(pattern(file))
  let typ = None
  use _ <- do(nibble.token(Equals))
  use val <- do(expr(file))
  use end <- do(get_span(file))
  return(tao.let_(pat, typ, val, span.merge(start, end)))
}

fn test_(file: String) -> Parser(Stmt, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(RAngle))
  use exp <- do(expr(file))
  use pat <- do(pattern(file))
  use end <- do(get_span(file))
  let name = file <> ":" <> int.to_string(end.start_line)
  return(tao.test_(name, exp, pat, span.merge(start, end)))
}

fn pattern(file: String) -> Parser(Pattern, Token, Nil) {
  nibble.one_of([pint(file), pvar(file)])
}

fn pint(file: String) -> Parser(Pattern, Token, Nil) {
  use start <- do(get_span(file))
  use num <- do(take_int())
  use end <- do(get_span(file))
  return(tao.pint(num, span.merge(start, end)))
}

fn pvar(file: String) -> Parser(Pattern, Token, Nil) {
  use start <- do(get_span(file))
  use name <- do(take_ident())
  use end <- do(get_span(file))
  case name {
    "_" -> return(tao.pany(span.merge(start, end)))
    _ -> return(tao.pvar(name, span.merge(start, end)))
  }
}

fn expr(file: String) -> Parser(Expr, Token, Nil) {
  pratt.expression(
    one_of: [int(file, _), float(file, _), var(file, _), hole(file, _)],
    and_then: [
      pratt.infix_left(1, nibble.token(Add), op2(tao.Add)),
      pratt.infix_left(1, nibble.token(Sub), op2(tao.Sub)),
      pratt.infix_left(2, nibble.token(Mul), op2(tao.Mul)),
      pratt.infix_left(2, nibble.token(Div), op2(tao.Div)),
    ],
    dropping: return(Nil),
  )
}

fn int(file: String, _) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use n <- do(take_int())
  use end <- do(get_span(file))
  return(tao.int(n, span.merge(start, end)))
}

fn float(file: String, _) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use num <- do(take_float())
  use end <- do(get_span(file))
  return(tao.float(num, span.merge(start, end)))
}

fn var(file: String, _) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use name <- do(take_ident())
  use end <- do(get_span(file))
  return(tao.var(name, span.merge(start, end)))
}

fn hole(file: String, _) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(Question))
  use end <- do(get_span(file))
  return(tao.hole(None, span.merge(start, end)))
}

fn op2(op: BinaryOp) -> fn(Expr, Expr) -> Expr {
  // There doesn't seem to be a way to get spans from nibble/pratt operators.
  let span = Span("", 0, 0, 0, 0)
  fn(lhs, rhs) { tao.op2(op, lhs, rhs, span) }
}

fn take_ident() -> Parser(String, Token, Nil) {
  nibble.take_map("an identifier", fn(tok) {
    case tok {
      Name(name) -> Some(name)
      _ -> None
    }
  })
}

fn take_int() -> Parser(Int, Token, Nil) {
  nibble.take_map("an integer", fn(tok) {
    case tok {
      IntLit(n) -> Some(n)
      _ -> None
    }
  })
}

fn take_float() -> Parser(Float, Token, Nil) {
  nibble.take_map("a float", fn(tok) {
    case tok {
      FloatLit(f) -> Some(f)
      _ -> None
    }
  })
}

fn get_span(file: String) -> Parser(Span, Token, Nil) {
  use s <- do(nibble.span())
  return(Span(file, s.row_start, s.col_start, s.row_end, s.col_end))
}
