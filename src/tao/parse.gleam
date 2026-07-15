import core/error as e
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result.{try}
import gleam/set
import gleam/string
import nibble.{type Parser, do, return}
import nibble/lexer.{type Lexer}
import nibble/pratt
import syntax/span.{type Span, Span, merge}
import tao/ast.{
  type BinaryOp, type Case, type Expr, type OverloadChoice, type Pattern,
  type Stmt, type UnaryOp,
} as tao

const reserved = [
  "import",
  "as",
  "fn",
  "let",
  "mut",
  "match",
  "if",
  "else",
  "error",
]

pub type Token {
  // Keywords
  KwImport
  KwAs
  KwFn
  KwLet
  KwMut
  KwMatch
  KwIf
  KwElse
  KwError

  // Values
  Name(String)
  IntLit(Int)
  FloatLit(Float)

  // Symbols
  Repl
  FatArrow
  ThinArrow
  TildeArrow
  Spread
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
  Question
  Pipe
  At
  Percent

  // Operators
  Add
  Sub
  Mul
  Div
}

// ============================================================================
// LEXER
// ============================================================================

pub fn lex(
  file: String,
  source: String,
) -> Result(List(lexer.Token(Token)), e.Error) {
  case lexer.run(source, lexer_()) {
    Ok(tokens) -> Ok(tokens)
    Error(lexer.NoMatchFound(row, col, lexeme)) -> {
      let span = Span(file, row, col, row, col)
      let ch = string.first(lexeme) |> result.unwrap(lexeme)
      Error(e.Error(e.UnexpectedToken(ch), span, []))
    }
  }
}

fn lexer_() -> Lexer(Token, Nil) {
  lexer.simple([
    // Keywords (all reserved words must have a keyword rule)
    lexer.keyword("import", "\\W", KwImport),
    lexer.keyword("as", "\\W", KwAs),
    lexer.keyword("fn", "\\W", KwFn),
    lexer.keyword("let", "\\W", KwLet),
    lexer.keyword("mut", "\\W", KwMut),
    lexer.keyword("match", "\\W", KwMatch),
    lexer.keyword("if", "\\W", KwIf),
    lexer.keyword("else", "\\W", KwElse),
    lexer.keyword("error", "\\W", KwError),

    // Names
    lexer.identifier("[_a-zA-Z]", "[_\\w]", set.from_list(reserved), Name),

    // Int and Float literals
    lexer.number(IntLit, FloatLit),

    // Single-line comments (// to end of line)
    lexer.comment("//", fn(_) { Nil }) |> lexer.ignore,

    // Two-character symbols (must come before single-char)
    lexer.token(">>>", Repl),
    lexer.token("=>", FatArrow),
    lexer.token("->", ThinArrow),
    lexer.token("~>", TildeArrow),
    lexer.token("..", Spread),

    // Single-character symbols
    lexer.token("(", LParen),
    lexer.token(")", RParen),
    lexer.token("{", LBrace),
    lexer.token("}", RBrace),
    lexer.token("<", LAngle),
    lexer.symbol(">", "[^>]", RAngle),
    lexer.token("[", LBracket),
    lexer.token("]", RBracket),
    lexer.token(":", Colon),
    lexer.token(";", Semicolon),
    lexer.token(",", Comma),
    lexer.symbol(".", "[^.]", Dot),
    lexer.symbol("=", "[^>]", Equals),
    lexer.token("?", Question),
    lexer.token("|", Pipe),
    lexer.token("@", At),
    lexer.token("%", Percent),

    lexer.token("+", Add),
    lexer.symbol("-", "[^>]", Sub),
    lexer.token("*", Mul),
    lexer.symbol("/", "[^/]", Div),

    // Whitespace
    lexer.whitespace(Nil) |> lexer.ignore,
  ])
}

// ============================================================================
// PUBLIC API
// ============================================================================

pub fn expression(file: String, source: String) -> Result(Expr, e.Error) {
  use tokens <- try(lex(file, source))
  case
    nibble.run(tokens, {
      use ast <- do(expr(file))
      use _ <- do(nibble.eof())
      return(ast)
    })
  {
    Ok(expr) -> Ok(expr)
    Error(dead_ends) -> Error(dead_ends_to_error(file, dead_ends))
  }
}

pub fn statements(file: String, source: String) -> Result(List(Stmt), e.Error) {
  use tokens <- try(lex(file, source))
  case
    nibble.run(tokens, {
      use stmts <- do(nibble.many(stmt(file)))
      use _ <- do(nibble.eof())
      return(stmts)
    })
  {
    Ok(stmts) -> Ok(stmts)
    Error(dead_ends) -> Error(dead_ends_to_error(file, dead_ends))
  }
}

// ============================================================================
// ERROR CONVERSION
// ============================================================================

/// Convert the best nibble DeadEnd into a core/error.Error.
///
/// Picks the first dead-end (closest to the failure point) and converts
/// its [`nibble.DeadEnd`](https://hexdocs.pm/nibble/nibble/nibble.html#DeadEnd)
/// into a structured [`Error`](../error#error) with trace breadcrumbs.
fn dead_ends_to_error(
  file: String,
  dead_ends: List(nibble.DeadEnd(Token, String)),
) -> e.Error {
  case dead_ends {
    [] ->
      e.Error(
        e.SyntaxError("internal error: no dead ends to report"),
        Span(file, 0, 0, 0, 0),
        [],
      )
    [first, ..] -> dead_end_to_error(file, first)
  }
}

fn dead_end_to_error(
  file: String,
  dead_end: nibble.DeadEnd(Token, String),
) -> e.Error {
  let pos = dead_end.pos
  let span = Span(file, pos.row_start, pos.col_start, pos.row_end, pos.col_end)
  // Extract context labels from nibble and create trace entries.
  // Since nibble's context is List(#(String, String)) (label + description)
  // and does not store per-entry spans, we use the error span for all
  // trace entries. The trace still provides useful nesting context.
  let trace =
    list.map(dead_end.context, fn(entry) {
      case entry {
        #(pos, label) -> {
          let span =
            Span(file, pos.row_start, pos.col_start, pos.row_end, pos.col_end)
          #(label, span)
        }
      }
    })

  case dead_end.problem {
    nibble.Expected(expecting, got) ->
      e.Error(e.ExpectedToken(expecting, token_to_string(got)), span, trace)

    nibble.Unexpected(tok) ->
      e.Error(e.UnexpectedToken(token_to_string(tok)), span, trace)

    nibble.EndOfInput -> e.Error(e.UnexpectedEndOfInput, span, trace)

    nibble.Custom(message) -> e.Error(e.SyntaxError(message), span, trace)

    nibble.BadParser(message) ->
      e.Error(e.SyntaxError("internal parser error: " <> message), span, trace)
  }
}

fn token_to_string(tok: Token) -> String {
  case tok {
    KwImport -> "import"
    KwAs -> "as"
    KwFn -> "fn"
    KwLet -> "let"
    KwMut -> "mut"
    KwMatch -> "match"
    KwIf -> "if"
    KwElse -> "else"
    KwError -> "error"
    Name(n) -> n
    IntLit(n) -> int.to_string(n)
    FloatLit(f) -> float.to_string(f)
    Repl -> ">>>"
    FatArrow -> "=>"
    ThinArrow -> "->"
    TildeArrow -> "~>"
    Spread -> ".."
    LParen -> "("
    RParen -> ")"
    LBrace -> "{"
    RBrace -> "}"
    LBracket -> "["
    RBracket -> "]"
    LAngle -> "<"
    RAngle -> ">"
    Colon -> ":"
    Semicolon -> ";"
    Comma -> ","
    Dot -> "."
    Equals -> "="
    Question -> "?"
    Pipe -> "|"
    At -> "@"
    Percent -> "%"
    Add -> "+"
    Sub -> "-"
    Mul -> "*"
    Div -> "/"
  }
}

// ============================================================================
// STATEMENT PARSERS
// ============================================================================

fn stmt(file: String) -> Parser(Stmt, Token, String) {
  nibble.one_of([
    let_(file),
    fn_def(file),
    test_(file),
  ])
  |> nibble.in("statement")
}

fn let_(file: String) -> Parser(Stmt, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwLet))
    use pat <- do(pattern(file))
    let typ = None
    use _ <- do(nibble.token(Equals))
    use val <- do(expr(file))
    use end <- do(get_span(file))
    return(tao.let_(pat, typ, val, merge(start, end)))
  }
  |> nibble.in("let binding")
}

fn fn_def(file: String) -> Parser(Stmt, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwFn))
    use name <- do(var_name(file))
    nibble.one_of([
      fn_def_body(file, start, name),
      fn_overload(file, start, name),
    ])
  }
  |> nibble.in("function definition")
}

fn fn_def_body(
  file: String,
  start: Span,
  name: String,
) -> Parser(Stmt, Token, String) {
  {
    use _ <- do(nibble.token(LParen))
    // TODO: implicit arguments
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
          // Fn expression definition: fn f(x) = expr
          use _ <- do(nibble.token(Equals))
          expr(file)
        },
        // Fn block definition: fn f(x) { stmts }
        {
          use _ <- do(nibble.token(LBrace))
          use stmts <- do(nibble.many(stmt(file)))
          use _ <- do(nibble.token(RBrace))
          return(tao.do(stmts, start))
        },
      ]),
    )
    use end <- do(get_span(file))
    return(tao.fn_def(
      name,
      implicits,
      params,
      opt_return,
      body,
      merge(start, end),
    ))
  }
  |> nibble.in("function body")
}

fn fn_overload(
  file: String,
  start: Span,
  name: String,
) -> Parser(Stmt, Token, String) {
  {
    use _ <- do(nibble.token(LBrace))
    use choices <- do(
      nibble.many({
        use _ <- do(nibble.token(Pipe))
        use start <- do(get_span(file))
        use opt_module <- do(
          nibble.optional({
            use mod <- do(var_name(file))
            use _ <- do(nibble.token(Dot))
            return(mod)
          }),
        )
        use name <- do(var_name(file))
        use _ <- do(nibble.token(LParen))
        use args <- do(arguments_pat(file))
        use _ <- do(nibble.token(RParen))
        use opt_guard <- do(nibble.optional(guard(file)))
        use end <- do(get_span(file))
        let s = merge(start, end)
        return(tao.OverloadChoice(opt_module, name, args, opt_guard, s))
      }),
    )
    use _ <- do(nibble.token(RBrace))
    use end <- do(get_span(file))
    return(tao.fn_overload(name, choices, merge(start, end)))
  }
  |> nibble.in("function overload")
}

fn test_(file: String) -> Parser(Stmt, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(Repl))
    use exp <- do(expr(file))
    use pat <- do(pattern(file))
    use end <- do(get_span(file))
    let name = file <> ":" <> int.to_string(end.start_line)
    return(tao.test_(name, exp, pat, merge(start, end)))
  }
  |> nibble.in("test expression")
}

// ============================================================================
// PATTERN PARSERS
// ============================================================================

fn pattern(file: String) -> Parser(Pattern, Token, String) {
  nibble.one_of([
    pfloat(file),
    pint(file),
    pvar(file),
    pctr(file),
  ])
}

fn pint(file: String) -> Parser(Pattern, Token, String) {
  use start <- do(get_span(file))
  use num <- do(take_int())
  use end <- do(get_span(file))
  return(tao.pint(num, merge(start, end)))
}

fn pfloat(file: String) -> Parser(Pattern, Token, String) {
  use start <- do(get_span(file))
  use num <- do(take_float())
  use end <- do(get_span(file))
  return(tao.pfloat(num, merge(start, end)))
}

fn pvar(file: String) -> Parser(Pattern, Token, String) {
  use start <- do(get_span(file))
  use name <- do(var_name(file))
  use end <- do(get_span(file))
  case name {
    "_" -> return(tao.pany(merge(start, end)))
    _ -> return(tao.pvar(name, merge(start, end)))
  }
}

fn pctr(file: String) -> Parser(Pattern, Token, String) {
  use start <- do(get_span(file))
  use name <- do(take_tag())
  use opt_args <- do(
    nibble.optional({
      use _ <- do(nibble.token(LParen))
      use args <- do(arguments_pat(file))
      use _ <- do(nibble.token(RParen))
      return(args)
    }),
  )
  let args = option.unwrap(opt_args, [])
  use end <- do(get_span(file))
  return(tao.pctr(name, args, merge(start, end)))
}

// ============================================================================
// EXPRESSION PARSERS
// ============================================================================

fn expr(file: String) -> Parser(Expr, Token, String) {
  pratt.expression(
    one_of: [
      fn(_config) { atom(file) },
      fn(_config) { match(file) },
      fn(_config) { if_expr(file) },
    ],
    and_then: [
      pratt.infix_left(1, nibble.token(Add), op2(tao.Add)),
      pratt.infix_left(1, nibble.token(Sub), op2(tao.Sub)),
      pratt.infix_left(2, nibble.token(Mul), op2(tao.Mul)),
      pratt.infix_left(2, nibble.token(Div), op2(tao.Div)),
    ],
    dropping: return(Nil),
  )
  |> nibble.in("expression")
}

fn atom(file: String) -> Parser(Expr, Token, String) {
  use expr <- do(
    nibble.one_of([
      hole(file),
      float(file),
      int(file),
      var(file),
      ctr(file),
    ]),
  )
  nibble.one_of([
    app(file, expr),
    return(expr),
  ])
}

fn hole(file: String) -> Parser(Expr, Token, String) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(Question))
  use end <- do(get_span(file))
  return(tao.hole(None, merge(start, end)))
}

fn int(file: String) -> Parser(Expr, Token, String) {
  use start <- do(get_span(file))
  use n <- do(take_int())
  use end <- do(get_span(file))
  return(tao.int(n, merge(start, end)))
}

fn float(file: String) -> Parser(Expr, Token, String) {
  use start <- do(get_span(file))
  use num <- do(take_float())
  use end <- do(get_span(file))
  return(tao.float(num, merge(start, end)))
}

fn var_name(file: String) -> Parser(String, Token, String) {
  nibble.one_of([
    take_var(),
    {
      let ops = [Add, Sub, Mul, Div]
      let ops_names =
        list.map(ops, fn(op) {
          use _ <- do(nibble.token(op))
          return(token_to_string(op))
        })
      use _ <- do(nibble.token(LParen))
      use name <- do(nibble.one_of(ops_names))
      use _ <- do(nibble.token(RParen))
      return(name)
    },
  ])
}

fn var(file: String) -> Parser(Expr, Token, String) {
  use start <- do(get_span(file))
  use name <- do(var_name(file))
  use end <- do(get_span(file))
  return(tao.var(name, merge(start, end)))
}

fn ctr(file: String) -> Parser(Expr, Token, String) {
  use start <- do(get_span(file))
  use name <- do(take_tag())
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
  return(tao.ctr(name, args, merge(start, end)))
}

fn op2(op: BinaryOp) -> fn(Expr, Expr) -> Expr {
  // Merge the spans of the two operands to get a meaningful span
  // for the binary operator expression.
  fn(lhs, rhs) { tao.op2(op, lhs, rhs, merge(lhs.span, rhs.span)) }
}

fn app(file: String, fun: Expr) -> Parser(Expr, Token, String) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(LParen))
  use args <- do(arguments(file))
  use _ <- do(nibble.token(RParen))
  use end <- do(get_span(file))
  return(tao.app(fun, args, merge(start, end)))
}

fn match(file: String) -> Parser(Expr, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwMatch))
    use arg <- do(expr(file))
    use _ <- do(nibble.token(LBrace))
    use cases <- do(nibble.many(match_case(file)))
    use _ <- do(nibble.token(RBrace))
    use end <- do(get_span(file))
    return(tao.match(arg, cases, merge(start, end)))
  }
  |> nibble.in("match expression")
}

fn if_expr(file: String) -> Parser(Expr, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwIf))
    use cond <- do(expr(file))
    use then_body <- do(expr(file))
    use opt_else <- do(
      nibble.optional({
        use _ <- do(nibble.token(KwElse))
        expr(file)
      }),
    )
    use end <- do(get_span(file))
    // Represent if-else as a match expression under the hood
    // if-then-else -> match cond { | True => then | False => else }
    // if-then -> match cond { | True => then | _ => hole }
    case opt_else {
      Some(else_expr) -> {
        let true_case =
          tao.Case(tao.pctr("True", [], merge(start, start)), None, then_body)
        let false_case =
          tao.Case(tao.pctr("False", [], merge(start, start)), None, else_expr)
        return(tao.match(cond, [true_case, false_case], merge(start, end)))
      }
      None -> {
        let true_case =
          tao.Case(tao.pctr("True", [], merge(start, start)), None, then_body)
        let false_case =
          tao.Case(
            tao.pany(merge(start, start)),
            None,
            tao.hole(None, merge(start, start)),
          )
        return(tao.match(cond, [true_case, false_case], merge(start, end)))
      }
    }
  }
  |> nibble.in("if expression")
}

fn match_case(file: String) -> Parser(Case, Token, String) {
  {
    use _ <- do(nibble.token(Pipe))
    use pat <- do(pattern(file))
    use opt_guard <- do(nibble.optional(guard(file)))
    use _ <- do(nibble.token(FatArrow))
    use body <- do(expr(file))
    return(tao.Case(pat, opt_guard, body))
  }
  |> nibble.in("match case")
}

fn guard(file: String) -> Parser(#(Expr, Option(Pattern)), Token, String) {
  {
    use _ <- do(nibble.token(KwIf))
    use cond <- do(expr(file))
    use opt_pat <- do(
      nibble.optional({
        use _ <- do(nibble.token(KwMatch))
        pattern(file)
      }),
    )
    return(#(cond, opt_pat))
  }
  |> nibble.in("guard clause")
}

// ============================================================================
// TOKEN CONSUMERS
// ============================================================================

fn take_var() -> Parser(String, Token, String) {
  nibble.take_map("a variable name", fn(tok) {
    case tok {
      Name("_") -> Some("_")
      Name(name) ->
        case is_tag_name(name) {
          True -> None
          False -> Some(name)
        }
      _ -> None
    }
  })
}

fn take_tag() -> Parser(String, Token, String) {
  nibble.take_map("a tag name", fn(tok) {
    case tok {
      Name(name) ->
        case is_tag_name(name) {
          True -> Some(name)
          False -> None
        }
      _ -> None
    }
  })
}

fn take_int() -> Parser(Int, Token, String) {
  nibble.take_map("an integer", fn(tok) {
    case tok {
      IntLit(n) -> Some(n)
      _ -> None
    }
  })
}

fn take_float() -> Parser(Float, Token, String) {
  nibble.take_map("a float", fn(tok) {
    case tok {
      FloatLit(f) -> Some(f)
      _ -> None
    }
  })
}

// ============================================================================
// ARGUMENT PARSERS
// ============================================================================

fn arguments(file: String) -> Parser(List(#(String, Expr)), Token, String) {
  nibble.many({
    use opt_name <- do(
      nibble.optional({
        use name <- do(var_name(file))
        use _ <- do(nibble.token(Colon))
        return(name)
      }),
    )
    use arg <- do(expr(file))
    return(#(option.unwrap(opt_name, ""), arg))
  })
}

fn arguments_pat(
  file: String,
) -> Parser(List(#(String, Pattern)), Token, String) {
  nibble.many({
    use opt_name <- do(
      nibble.optional({
        use name <- do(var_name(file))
        use _ <- do(nibble.token(Colon))
        return(name)
      }),
    )
    use arg <- do(pattern(file))
    return(#(option.unwrap(opt_name, ""), arg))
  })
}

// ============================================================================
// HELPERS
// ============================================================================

fn get_span(file: String) -> Parser(Span, Token, String) {
  use s <- do(nibble.span())
  return(Span(file, s.row_start, s.col_start, s.row_end, s.col_end))
}

fn is_tag_name(name: String) -> Bool {
  case string.pop_grapheme(name) {
    Ok(#("_", _)) -> is_tag_name(name)
    Ok(#(first, _)) -> first == string.uppercase(first)
    _ -> False
  }
}
