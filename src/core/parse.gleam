/// Core Language Parser
///
/// Parses Core source text into AST using the nibble parser combinator library.
import core/ast.{
  type Case, type Expr, type Pattern, type TypeDefinition, type Variant,
}
import core/error as e
import core/literals.{type LiteralType} as lit
import gleam/option.{type Option, None, Some}
import gleam/result.{try}
import gleam/set
import nibble.{type Parser, do, return}
import nibble/lexer.{type Lexer}
import syntax/span.{type Span, Span}

// ============================================================================
// TOKEN DEFINITIONS
// ============================================================================

pub type Token {
  // Keywords
  KwType
  KwIntT
  KwFloatT
  KwI8
  KwI16
  KwI32
  KwI64
  KwU8
  KwU16
  KwU32
  KwU64
  KwF16
  KwF32
  KwF64
  KwFn
  KwPi
  KwLet
  KwMatch
  KwFix
  KwError

  // Values
  Name(String)
  IntLit(Int)
  FloatLit(Float)

  // Symbols
  AnnOpen
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
  Spread
  Pipe
  Tilde
  Question
  At
  Hash
}

// ============================================================================
// PUBLIC API
// ============================================================================

pub fn lex(
  file: String,
  source: String,
) -> Result(List(lexer.Token(Token)), e.Error) {
  case lexer.run(source, core_lexer()) {
    Ok(tokens) -> Ok(tokens)
    Error(lexer.NoMatchFound(row, col, lexeme)) -> {
      let span = Span(file, row, col, row, col)
      let err = e.Error(e.UnexpectedToken(lexeme), span, [])
      Error(err)
    }
  }
}

pub fn parse(file: String, source: String) -> Result(Expr, e.Error) {
  use tokens <- try(lex(file, source))
  case nibble.run(tokens, expr(file)) {
    Ok(ast) -> Ok(ast)
    Error(dead_ends) ->
      case dead_ends {
        // TODO: use all dead_ends, not just the first
        [dead_end, ..] -> {
          let span =
            Span(
              file,
              dead_end.pos.row_start,
              dead_end.pos.col_start,
              dead_end.pos.row_end,
              dead_end.pos.col_end,
            )
          // TODO: make this into a more specific error
          let err = e.Error(e.UnexpectedToken("syntax error"), span, [])
          Error(err)
        }
        _ -> {
          let span = Span(file, 0, 0, 0, 0)
          // TODO: make this into a more specific error
          let err = e.Error(e.UnexpectedToken("syntax error"), span, [])
          Error(err)
        }
      }
  }
}

// ============================================================================
// LEXER
// ============================================================================

fn core_lexer() -> Lexer(Token, Nil) {
  lexer.simple([
    // Keywords with % prefix
    lexer.keyword("%Type", "\\W", KwType),
    lexer.keyword("%Int", "\\W", KwIntT),
    lexer.keyword("%Float", "\\W", KwFloatT),
    lexer.keyword("%I8", "\\W", KwI8),
    lexer.keyword("%I16", "\\W", KwI16),
    lexer.keyword("%I32", "\\W", KwI32),
    lexer.keyword("%I64", "\\W", KwI64),
    lexer.keyword("%U8", "\\W", KwU8),
    lexer.keyword("%U16", "\\W", KwU16),
    lexer.keyword("%U32", "\\W", KwU32),
    lexer.keyword("%U64", "\\W", KwU64),
    lexer.keyword("%F16", "\\W", KwF16),
    lexer.keyword("%F32", "\\W", KwF32),
    lexer.keyword("%F64", "\\W", KwF64),

    lexer.keyword("%lam", "\\W", KwFn),
    lexer.keyword("%pi", "\\W", KwPi),
    lexer.keyword("%let", "\\W", KwLet),
    lexer.keyword("%match", "\\W", KwMatch),
    lexer.keyword("%fix", "\\W", KwFix),
    lexer.keyword("%error", "\\W", KwError),

    // Names
    lexer.identifier("[_a-zA-Z]", "[_\\w]", set.new(), Name),

    // Int and Float literals
    lexer.number(IntLit, FloatLit),

    // Single-line comments (// to end of line)
    lexer.comment("//", fn(_) { Nil }) |> lexer.ignore,

    // Two-character symbols (must come before single-char)
    lexer.token("%(", AnnOpen),
    lexer.token("=>", FatArrow),
    lexer.token("->", ThinArrow),
    lexer.token("..", Spread),
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
    lexer.symbol(".", "[^.]", Dot),
    lexer.symbol("=", "[^>]", Equals),
    lexer.token("|", Pipe),
    lexer.token("~", Tilde),
    lexer.token("?", Question),
    lexer.token("@", At),
    lexer.token("#", Hash),

    // Whitespace
    lexer.whitespace(Nil) |> lexer.ignore,
  ])
}

// ============================================================================
// PARSER
// ============================================================================

fn expr(file: String) -> Parser(Expr, Token, Nil) {
  use fun <- do(
    nibble.one_of([
      typ(file),
      hole(file),
      int(file),
      float(file),
      lit_t(file),
      var(file),
      tag(file),
      rcd(file),
      ann(file),
      lam(file),
      pi_expr(file),
      fix(file),
      let_(file),
      // match_expr(file),
    // error_expr(file),
    // builtin_call(file),
    // paren_expr(file),
    ]),
  )
  nibble.one_of([
    {
      // Function application: f(x)
      use _ <- do(nibble.token(LParen))
      use arg <- do(expr(file))
      use _ <- do(nibble.token(RParen))
      return(ast.app(fun, arg, span.merge(fun.span, arg.span)))
    },
    // No application
    return(fun),
  ])
}

fn typ(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(KwType))
  use universe <- do(
    nibble.one_of([
      angle_brackets(take_int()),
      return(0),
    ]),
  )
  use end <- do(get_span(file))
  return(ast.typ(universe, span.merge(start, end)))
}

fn hole(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(Question))
  use id <- do(nibble.optional(take_int()))
  use end <- do(get_span(file))
  return(ast.hole(id, span.merge(start, end)))
}

fn int(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use n <- do(take_int())
  use end <- do(get_span(file))
  return(ast.int(n, span.merge(start, end)))
}

fn float(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use num <- do(take_float())
  use end <- do(get_span(file))
  return(ast.float(num, span.merge(start, end)))
}

fn lit_t(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use type_ <- do(take_lit_type())
  use end <- do(get_span(file))
  return(ast.lit_t(type_, span.merge(start, end)))
}

fn var(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use name <- do(take_ident())
  use end <- do(get_span(file))
  return(ast.var(name, span.merge(start, end)))
}

fn tag(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(Hash))
  use tag <- do(take_ident())
  use _ <- do(nibble.token(LParen))
  use arg <- do(expr(file))
  use _ <- do(nibble.token(RParen))
  use end <- do(get_span(file))
  return(ast.ctr(tag, arg, span.merge(start, end)))
}

fn rcd(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(LBrace))
  use fields <- do(
    nibble.one_of([
      comma_separated({
        use name <- do(take_ident())
        use value <- do(
          nibble.optional({
            use _ <- do(nibble.token(Colon))
            expr(file)
          }),
        )
        use default <- do(
          nibble.optional({
            use _ <- do(nibble.token(Equals))
            expr(file)
          }),
        )
        return(#(name, #(value, default)))
      }),
      return([]),
    ]),
  )
  use tail <- do(
    nibble.optional({
      use _ <- do(nibble.token(Spread))
      nibble.one_of([
        expr(file),
        return(ast.var("", start)),
      ])
    }),
  )
  use _ <- do(nibble.token(RBrace))
  use end <- do(get_span(file))
  return(ast.rcd(fields, tail, span.merge(start, end)))
}

fn ann(file: String) -> Parser(Expr, Token, Nil) {
  use _ <- do(nibble.token(AnnOpen))
  use value <- do(expr(file))
  use _ <- do(nibble.token(Colon))
  use typ <- do(expr(file))
  use _ <- do(nibble.token(RParen))
  return(ast.ann(value, typ, span.merge(value.span, typ.span)))
}

fn lam(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(KwFn))
  use _ <- do(nibble.token(LParen))
  use name <- do(take_ident())
  use type_ <- do(optional_type(file))
  use _ <- do(nibble.token(RParen))
  use _ <- do(nibble.token(FatArrow))
  use body <- do(expr(file))
  use end <- do(get_span(file))
  return(ast.lam(#(name, type_), body, span.merge(start, end)))
}

fn pi_expr(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(KwPi))
  use _ <- do(nibble.token(LParen))
  use name <- do(take_ident())
  use type_ <- do(optional_type(file))
  use _ <- do(nibble.token(RParen))
  use _ <- do(nibble.token(ThinArrow))
  use body <- do(expr(file))
  use end <- do(get_span(file))
  return(ast.pi(#(name, type_), body, span.merge(start, end)))
}

fn fix(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(KwFix))
  use name <- do(take_ident())
  use _ <- do(nibble.token(Dot))
  use body <- do(expr(file))
  use end <- do(get_span(file))
  return(ast.fix(name, body, span.merge(start, end)))
}

fn let_(file: String) -> Parser(Expr, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(KwLet))
  use name <- do(take_ident())
  use _ <- do(nibble.token(Colon))
  use type_ <- do(nibble.optional(expr(file)))
  use _ <- do(nibble.token(Equals))
  use value <- do(expr(file))
  use _ <- do(nibble.optional(nibble.token(Semicolon)))
  use body <- do(expr(file))
  use end <- do(get_span(file))
  return(ast.let_var(#(name, type_, value), body, span.merge(start, end)))
}

// ============================================================================
// HELPERS
// ============================================================================

fn get_span(file: String) -> Parser(Span, Token, Nil) {
  use s <- do(nibble.span())
  return(Span(file, s.row_start, s.col_start, s.row_end, s.col_end))
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

fn take_lit_type() -> Parser(LiteralType, Token, Nil) {
  nibble.take_map("a literal type", fn(tok) {
    case tok {
      KwIntT -> Some(lit.IntT)
      KwFloatT -> Some(lit.FloatT)
      KwI8 -> Some(lit.I8)
      KwI16 -> Some(lit.I16)
      KwI32 -> Some(lit.I32)
      KwI64 -> Some(lit.I64)
      KwU8 -> Some(lit.U8)
      KwU16 -> Some(lit.U16)
      KwU32 -> Some(lit.U32)
      KwU64 -> Some(lit.U64)
      KwF16 -> Some(lit.F16)
      KwF32 -> Some(lit.F32)
      KwF64 -> Some(lit.F64)
      _ -> None
    }
  })
}

fn angle_brackets(parser: Parser(a, Token, Nil)) -> Parser(a, Token, Nil) {
  use _ <- do(nibble.token(LAngle))
  use n <- do(parser)
  use _ <- do(nibble.token(RAngle))
  return(n)
}

fn comma_separated(item: Parser(a, Token, Nil)) -> Parser(List(a), Token, Nil) {
  use first <- do(item)
  use rest <- do(
    nibble.many({
      use _ <- do(nibble.token(Comma))
      use next <- do(item)
      return(next)
    }),
  )
  return([first, ..rest])
}

fn optional_type(file: String) -> Parser(Option(Expr), Token, Nil) {
  nibble.optional({
    use _ <- do(nibble.token(Colon))
    expr(file)
  })
}
