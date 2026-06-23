import gleam/int
import gleam/io
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
import tao/ast.{
  type BinaryOp, type Case, type Expr, type Pattern, type Stmt, type UnaryOp,
} as tao
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
  TildeArrow
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
    Error(errors) -> {
      io.println_error("")
      io.println_error("❌ SYNTAX ERROR: src/tao/parse.gleam::statements")
      list.map(errors, fn(err) {
        let msg =
          file
          <> ":"
          <> int.to_string(err.pos.row_start)
          <> ":"
          <> int.to_string(err.pos.col_start)
          <> ": "
          <> string.inspect(err.problem)
        io.println_error(msg)
      })
      io.println_error("")
      todo as "convert syntax errors into tao/error.Error, bubble up and defer reporting"
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
    lexer.keyword("mut", "\\W", KwMut),
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
    lexer.token("~>", TildeArrow),
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

    lexer.token("+", Add),
    lexer.symbol("-", "[^>]", Sub),
    lexer.token("*", Mul),
    lexer.token("/", Div),

    // Whitespace
    lexer.whitespace(Nil) |> lexer.ignore,
  ])
}

fn stmt(file: String) -> Parser(Stmt, Token, Nil) {
  nibble.one_of([let_(file), fn_def(file), test_(file)])
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

fn fn_def(file: String) -> Parser(Stmt, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(KwFn))
  use name <- do(take_ident())
  use _ <- do(nibble.token(LParen))
  use implicits <- do(return([]))
  use params <- do(nibble.sequence(
    {
      use pattern <- do(pattern(file))
      use opt_type <- do(
        nibble.optional({
          use _ <- do(nibble.token(Colon))
          expr(file)
        }),
      )
      use opt_default <- do(
        nibble.optional({
          use _ <- do(nibble.token(Equals))
          expr(file)
        }),
      )
      return(#(pattern, #(opt_type, opt_default)))
    },
    nibble.token(Comma),
  ))
  use _ <- do(nibble.token(RParen))
  use opt_return <- do(
    nibble.optional({
      use _ <- do(nibble.token(ThinArrow))
      expr(file)
    }),
  )
  use body <- do(
    nibble.one_of([
      {
        // Fn expression definition
        use _ <- do(nibble.token(Equals))
        expr(file)
      },
      // Fn block definition
    ]),
  )
  use end <- do(get_span(file))
  return(tao.fn_def(
    name,
    implicits,
    params,
    opt_return,
    body,
    span.merge(start, end),
  ))
}

fn test_(file: String) -> Parser(Stmt, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(RAngle))
  use exp <- do(expr(file))
  use _ <- do(nibble.optional(nibble.token(TildeArrow)))
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
    one_of: [
      fn(_config) { atom(file) },
      fn(_config) { match(file) },
    ],
    and_then: [
      pratt.infix_left(1, nibble.token(Add), op2(tao.Add)),
      pratt.infix_left(1, nibble.token(Sub), op2(tao.Sub)),
      pratt.infix_left(2, nibble.token(Mul), op2(tao.Mul)),
      pratt.infix_left(2, nibble.token(Div), op2(tao.Div)),
    ],
    dropping: return(Nil),
  )
}

fn atom(file: String) -> Parser(Expr, Token, Nil) {
  use expr <- do(
    nibble.one_of([
      hole(file),
      int(file),
      float(file),
      var_or_ctr(file),
    ]),
  )
  nibble.one_of([
    app(file, expr),
    return(expr),
  ])
}

fn hole(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(Question))
  use end <- do(get_span(file))
  return(tao.hole(None, span.merge(start, end)))
}

fn int(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use n <- do(take_int())
  use end <- do(get_span(file))
  return(tao.int(n, span.merge(start, end)))
}

fn float(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use num <- do(take_float())
  use end <- do(get_span(file))
  return(tao.float(num, span.merge(start, end)))
}

fn var_or_ctr(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use name <- do(take_ident())
  case is_ctr_name(name) {
    True -> {
      use opt_args <- do(
        nibble.optional({
          use _ <- do(nibble.token(LParen))
          use args <- do(arguments(file))
          use _ <- do(nibble.token(RParen))
          return(args)
        }),
      )
      let args = option.unwrap(opt_args, [])
      use end <- do(get_span(file))
      return(tao.ctr(name, args, span.merge(start, end)))
    }
    False -> {
      use end <- do(get_span(file))
      return(tao.var(name, span.merge(start, end)))
    }
  }
}

fn is_ctr_name(name: String) -> Bool {
  case string.pop_grapheme(name) {
    Ok(#("_", _)) -> is_ctr_name(name)
    Ok(#(first, _)) -> first == string.uppercase(first)
    _ -> False
  }
}

fn op2(op: BinaryOp) -> fn(Expr, Expr) -> Expr {
  // There doesn't seem to be a way to get spans from nibble/pratt operators.
  let span = Span("", 0, 0, 0, 0)
  fn(lhs, rhs) { tao.op2(op, lhs, rhs, span) }
}

fn app(file: String, fun: Expr) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use #(implicit, close) <- do(
    nibble.one_of([
      nibble.token(LParen) |> nibble.map(fn(_) { #(False, RParen) }),
      nibble.token(LAngle) |> nibble.map(fn(_) { #(True, RAngle) }),
    ]),
  )
  use args <- do(arguments(file))
  use _ <- do(nibble.token(close))
  use end <- do(get_span(file))
  return(tao.app(implicit, fun, args, span.merge(start, end)))
}

fn match(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(KwMatch))
  use arg <- do(expr(file))
  use _ <- do(nibble.token(LBrace))
  use cases <- do(nibble.many(match_case(file)))
  use _ <- do(nibble.token(RBrace))
  use end <- do(get_span(file))
  return(tao.match(arg, cases, span.merge(start, end)))
}

fn match_case(file: String) -> Parser(Case, Token, Nil) {
  use _ <- do(nibble.token(Pipe))
  use pat <- do(pattern(file))
  use _ <- do(nibble.token(FatArrow))
  use body <- do(expr(file))
  return(tao.Case(pat, body))
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

fn arguments(file: String) -> Parser(List(#(String, Expr)), Token, Nil) {
  nibble.many({
    use opt_name <- do(
      nibble.optional({
        use name <- do(take_ident())
        use _ <- do(nibble.token(Colon))
        return(name)
      }),
    )
    use arg <- do(expr(file))
    return(#(option.unwrap(opt_name, ""), arg))
  })
}

fn get_span(file: String) -> Parser(Span, Token, Nil) {
  use s <- do(nibble.span())
  return(Span(file, s.row_start, s.col_start, s.row_end, s.col_end))
}
