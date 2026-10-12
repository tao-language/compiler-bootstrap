/// Tao Language Parser
///
/// Parses Tao source text into `tao/ast` statements/expressions using the
/// nibble parser combinator library. Tag names (constructor/type names)
/// start with an uppercase letter; everything else is a variable name.
/// 
/// By default, nibble parsers like one_of will not backtrack if they 
/// fail after consuming at least one token. Passing a parser to 
/// nibble.backtrackable will change this behavior and allows us to 
/// jump back to the state of the parser before it consumed any input 
/// and try another one.
import core/error as e
import filepath
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/regexp
import gleam/result.{try}
import gleam/set
import gleam/string
import nibble.{type Parser, do, return}
import nibble/lexer.{
  type Lexer, type Matcher, type Span as NibbleSpan, Keep, NoMatch, Skip,
}
import nibble/pratt
import syntax/span.{type Span, Span, merge}
import tao/ast.{
  type BinaryOp, type Case, type Expr, type Parameters, type Pattern, type Stmt,
} as tao

const reserved = [
  "import",
  "as",
  "extern",
  "fn",
  "let",
  "mut",
  "match",
  "if",
  "else",
  "type",
  // Named binary operators: lexed as operator tokens, not variable names.
  "and",
  "or",
  "is",
  "in",
]

pub type Token {
  // Keywords
  KwImport
  KwAs
  KwFn
  KwExtern
  KwLet
  KwMut
  KwMatch
  KwIf
  KwElse
  KwType

  // Values
  Name(String)
  IntLit(Int)
  FloatLit(Float)
  // An anonymous-function argument placeholder. `_` is `Placeholder(None)`
  // (the first argument); `_N` is `Placeholder(Some(N))` (the N-th argument,
  // 1-based). `_0` is a syntax error. Lexed as its own token so it can never
  // clash with a variable name.
  Placeholder(Option(Int))

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
  And
  Or
  Is
  In
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
    lexer.keyword("extern", "\\W", KwExtern),
    lexer.keyword("fn", "\\W", KwFn),
    lexer.keyword("let", "\\W", KwLet),
    lexer.keyword("mut", "\\W", KwMut),
    lexer.keyword("match", "\\W", KwMatch),
    lexer.keyword("if", "\\W", KwIf),
    lexer.keyword("else", "\\W", KwElse),
    lexer.keyword("type", "\\W", KwType),

    // Named binary operators (reserved, so `andy` still lexes as a name)
    lexer.keyword("and", "\\W", And),
    lexer.keyword("or", "\\W", Or),
    lexer.keyword("is", "\\W", Is),
    lexer.keyword("in", "\\W", In),

    // Placeholders (`_`, `_1`, `_2`, ...): an underscore followed by digits
    // only. Must come before the identifier rule so they are not lexed as
    // names (which would let a variable clash with a placeholder).
    placeholder_matcher(),

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

/// Lex `_` and `_N` (an underscore followed by digits only) as `Placeholder`.
/// `_foo`, `_1a` and the like are not placeholders and fall through to the
/// identifier rule.
fn placeholder_matcher() -> Matcher(Token, Nil) {
  let assert Ok(ident) = regexp.from_string("^_\\d*$")
  let assert Ok(digit) = regexp.from_string("\\d")
  let assert Ok(word) = regexp.from_string("\\w")
  lexer.custom(fn(mode, lexeme, lookahead) {
    case regexp.check(digit, lookahead), regexp.check(ident, lexeme) {
      True, True -> Skip
      // A word char follows (e.g. `_and`): it is a name, not a placeholder.
      False, True ->
        case regexp.check(word, lookahead) {
          True -> NoMatch
          False -> Keep(Placeholder(placeholder_index(lexeme)), mode)
        }
      _, _ -> NoMatch
    }
  })
}

/// `_` is `None` (the first argument); `_N` is `Some(N)`. The 1-based position
/// is resolved by the parser (`_0` is rejected there).
fn placeholder_index(lexeme: String) -> Option(Int) {
  let digits = string.drop_start(lexeme, 1)
  case digits {
    "" -> None
    _ -> int.parse(digits) |> result.map(Some) |> result.unwrap(None)
  }
}

// ============================================================================
// PUBLIC API
// ============================================================================

/// The outcome of parsing: a successful value, or the raw nibble dead ends
/// (every alternative that failed) for inspection by `debug-parse`.
pub type Outcome(a) {
  Parsed(a)
  ParseFailed(List(nibble.DeadEnd(Token, String)))
}

/// Parse a single Tao expression (used by the REPL/`-c`).
pub fn expression(file: String, source: String) -> Result(Expr, e.Error) {
  outcome_to_result(file, parse_expression(file, source))
}

/// Parse a whole Tao module into its top-level statements.
pub fn statements(file: String, source: String) -> Result(List(Stmt), e.Error) {
  outcome_to_result(file, parse_statements(file, source))
}

/// Parse a single Tao expression, keeping the raw dead ends on failure.
pub fn parse_expression(
  file: String,
  source: String,
) -> Result(Outcome(Expr), e.Error) {
  use tokens <- try(lex(file, source))
  Ok(
    case
      nibble.run(tokens, {
        use ast <- do(expr(file))
        use _ <- do(nibble.eof())
        return(ast)
      })
    {
      Ok(ast) -> Parsed(ast)
      Error(dead_ends) -> ParseFailed(dead_ends)
    },
  )
}

/// Parse a whole Tao module, keeping the raw dead ends on failure.
pub fn parse_statements(
  file: String,
  source: String,
) -> Result(Outcome(List(Stmt)), e.Error) {
  use tokens <- try(lex(file, source))
  Ok(
    case
      nibble.run(tokens, {
        use stmts <- do(nibble.many(stmt(file)))
        use _ <- do(nibble.eof())
        return(stmts)
      })
    {
      Ok(stmts) -> Parsed(stmts)
      Error(dead_ends) -> ParseFailed(dead_ends)
    },
  )
}

/// Lex the source into its token stream (with spans and lexemes), for
/// `debug-parse`.
pub fn tokens(
  file: String,
  source: String,
) -> Result(List(lexer.Token(Token)), e.Error) {
  lex(file, source)
}

fn outcome_to_result(
  file: String,
  outcome: Result(Outcome(a), e.Error),
) -> Result(a, e.Error) {
  case outcome {
    Error(err) -> Error(err)
    Ok(Parsed(value)) -> Ok(value)
    Ok(ParseFailed(dead_ends)) -> Error(dead_ends_to_error(file, dead_ends))
  }
}

// ============================================================================
// ERROR CONVERSION
// ============================================================================

/// Convert the best nibble DeadEnd into a core/error.Error.
///
/// Picks the dead end that made the most progress (the furthest position) and
/// converts its [`nibble.DeadEnd`](https://hexdocs.pm/nibble/nibble/nibble.html#DeadEnd)
/// into a structured [`Error`](../error#error) with trace breadcrumbs.
pub fn dead_ends_to_error(
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
    // A `one_of` records a dead end for every alternative it tried. The
    // alternatives that fail immediately (e.g. `import` when the input is a
    // `fn` definition) all point at the same starting token, which is
    // misleading. The most useful dead end is the one that made the most
    // progress, i.e. the one at the furthest position: it is the most
    // specific and points at the real problem.
    [first, ..] -> {
      let best = furthest_dead_end(first, dead_ends)
      dead_end_to_error(file, best)
    }
  }
}

/// Pick the dead end at the furthest position. On a position tie, prefer a
/// specific `Custom` message (e.g. "_0 is not a valid placeholder") over the
/// generic "expected X" dead ends a `one_of` records for every alternative.
fn furthest_dead_end(
  best: nibble.DeadEnd(Token, String),
  rest: List(nibble.DeadEnd(Token, String)),
) -> nibble.DeadEnd(Token, String) {
  list.fold(rest, best, fn(acc, dead_end) {
    case is_after(dead_end.pos, acc.pos) {
      True -> dead_end
      False ->
        case is_same_pos(dead_end.pos, acc.pos) {
          True ->
            case is_custom(dead_end), is_custom(acc) {
              True, False -> dead_end
              _, _ -> acc
            }
          False -> acc
        }
    }
  })
}

fn is_after(a: NibbleSpan, b: NibbleSpan) -> Bool {
  a.row_start > b.row_start
  || { a.row_start == b.row_start && a.col_start > b.col_start }
}

fn is_same_pos(a: NibbleSpan, b: NibbleSpan) -> Bool {
  a.row_start == b.row_start && a.col_start == b.col_start
}

fn is_custom(dead_end: nibble.DeadEnd(Token, String)) -> Bool {
  case dead_end.problem {
    nibble.Custom(_message) -> True
    _ -> False
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
      e.Error(
        e.ExpectedToken(friendly_expect(expecting), token_to_string(got)),
        span,
        trace,
      )

    nibble.Unexpected(tok) ->
      e.Error(e.UnexpectedToken(token_to_string(tok)), span, trace)

    nibble.EndOfInput -> e.Error(e.UnexpectedEndOfInput, span, trace)

    nibble.Custom(message) -> e.Error(e.SyntaxError(message), span, trace)

    nibble.BadParser(message) ->
      e.Error(e.SyntaxError("internal parser error: " <> message), span, trace)
  }
}

pub fn token_to_string(tok: Token) -> String {
  case tok {
    KwImport -> "import"
    KwAs -> "as"
    KwExtern -> "extern"
    KwFn -> "fn"
    KwLet -> "let"
    KwMut -> "mut"
    KwMatch -> "match"
    KwIf -> "if"
    KwElse -> "else"
    KwType -> "type"
    Name(n) -> n
    IntLit(n) -> int.to_string(n)
    FloatLit(f) -> float.to_string(f)
    Placeholder(n) ->
      case n {
        None -> "_"
        Some(n) -> "_" <> int.to_string(n)
      }
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
    And -> "and"
    Or -> "or"
    Is -> "is"
    In -> "in"
  }
}

/// Nibble reports the expected token as `string.inspect(token)`, which for a
/// symbol/keyword is just the constructor name (e.g. `"RParen"`). Map those
/// back to their source spelling. Strings produced by `take_map` (e.g. `"a
/// name"`) and payload tokens (e.g. `Name("foo")`) are already readable and
/// fall through unchanged.
fn friendly_expect(s: String) -> String {
  case s {
    "KwImport" -> "import"
    "KwAs" -> "as"
    "KwExtern" -> "extern"
    "KwFn" -> "fn"
    "KwLet" -> "let"
    "KwMut" -> "mut"
    "KwMatch" -> "match"
    "KwIf" -> "if"
    "KwElse" -> "else"
    "KwType" -> "type"
    "Repl" -> ">>>"
    "FatArrow" -> "=>"
    "ThinArrow" -> "->"
    "TildeArrow" -> "~>"
    "Spread" -> ".."
    "LParen" -> "("
    "RParen" -> ")"
    "LBrace" -> "{"
    "RBrace" -> "}"
    "LBracket" -> "["
    "RBracket" -> "]"
    "LAngle" -> "<"
    "RAngle" -> ">"
    "Colon" -> ":"
    "Semicolon" -> ";"
    "Comma" -> ","
    "Dot" -> "."
    "Equals" -> "="
    "Question" -> "?"
    "Pipe" -> "|"
    "At" -> "@"
    "Percent" -> "%"
    "Add" -> "+"
    "Sub" -> "-"
    "Mul" -> "*"
    "Div" -> "/"
    "And" -> "and"
    "Or" -> "or"
    "Is" -> "is"
    "In" -> "in"
    _ -> s
  }
}

// ============================================================================
// STATEMENT PARSERS
// ============================================================================

fn stmt(file: String) -> Parser(Stmt, Token, String) {
  nibble.one_of([
    import_(file),
    extern(file),
    let_var(file),
    let_pat(file),
    fn_def(file),
    type_def(file),
    test_(file),
  ])
}

/// A type definition: `type Name(p1: t1, p2, ...) { | Tag1(...) -> ... | ... }`
fn type_def(file: String) -> Parser(Stmt, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwType))
    use name <- do(take_tag())
    use opt_params <- do(
      nibble.optional({
        use _ <- do(nibble.token(LParen))
        use params <- do(sequence(type_parameter(file), Comma))
        use _ <- do(nibble.token(RParen))
        return(params)
      }),
    )
    let params = option.unwrap(opt_params, [])
    use _ <- do(nibble.token(LBrace))
    use variants <- do(nibble.many(variant(file, name, params)))
    use _ <- do(nibble.token(RBrace))
    use end <- do(get_span(file))
    return(tao.Stmt(
      tao.TypeDef(name, tao.TypeDefinition(params, variants)),
      merge(start, end),
    ))
  }
  |> nibble.in("type definition")
}

/// A type parameter: `a`, `a: Type`, `n: Int` — a name with an optional
/// type annotation (untyped parameters are plain type variables).
fn type_parameter(
  file: String,
) -> Parser(#(String, Option(tao.Type)), Token, String) {
  use name <- do(var_name())
  use opt_type <- do(
    nibble.optional({
      use _ <- do(nibble.token(Colon))
      expr(file)
    }),
  )
  return(#(name, opt_type))
}

/// A variant: `| Tag<p1, ...>(x: t1, ...) -> returns` where the
/// parameters (GADT), arguments and return type are all optional. A
/// variant without an explicit return type returns the enclosing type
/// applied to its parameters.
fn variant(
  file: String,
  type_name: String,
  type_params: List(#(String, Option(tao.Type))),
) -> Parser(tao.Variant, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(Pipe))
    use tag <- do(take_tag())
    use opt_params <- do(
      nibble.optional({
        use _ <- do(nibble.token(LAngle))
        use params <- do(sequence(type_parameter(file), Comma))
        use _ <- do(nibble.token(RAngle))
        return(params)
      }),
    )
    let params = option.unwrap(opt_params, [])
    use opt_args <- do(
      nibble.optional({
        use _ <- do(nibble.token(LParen))
        use args <- do(arguments(file, expr(file)))
        use _ <- do(nibble.token(RParen))
        return(args)
      }),
    )
    let args = option.unwrap(opt_args, [])
    use opt_returns <- do(
      nibble.optional({
        use _ <- do(nibble.token(ThinArrow))
        expr(file)
      }),
    )
    let returns = case opt_returns {
      Some(returns) -> returns
      None ->
        tao.ctr(
          type_name,
          list.map(type_params, fn(param) {
            let #(pname, _) = param
            #(pname, tao.var(pname, start))
          }),
          start,
        )
    }
    use _end <- do(get_span(file))
    return(tao.Variant(tag, params, args, returns))
  }
  |> nibble.in("type variant")
}

fn import_(file: String) -> Parser(Stmt, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwImport))
    use path <- do(import_path())
    use alias <- do(
      nibble.one_of([
        import_alias(),
        return(filepath.base_name(path)),
      ]),
    )
    use scope <- do(
      nibble.one_of([
        {
          use _ <- do(nibble.token(Mul))
          return(tao.ImportAll)
        },
        {
          use _ <- do(nibble.token(LBrace))
          use names <- do(sequence(import_name(), Comma))
          use _ <- do(nibble.token(RBrace))
          return(tao.ImportSome(names))
        },
        return(tao.ImportSome([])),
      ]),
    )
    use end <- do(get_span(file))
    return(tao.Stmt(tao.Import(path, alias, scope), span.merge(start, end)))
  }
  |> nibble.in("import statement")
}

fn import_path() -> Parser(String, Token, String) {
  let path_valid = [
    take_var(),
    token_text(Div),
    token_text(Sub),
    token_text(Dot),
    nibble.map(take_int(), int.to_string),
  ]
  nibble.one_of([
    // Relative: ./path
    {
      use _ <- do(nibble.token(Dot))
      use _ <- do(nibble.token(Div))
      use parts <- do(nibble.many1(nibble.one_of(path_valid)))
      return("./" <> string.join(parts, ""))
    },
    // Relative: ../path (one or more ../)
    {
      use dots <- do(
        nibble.many1({
          use _ <- do(nibble.token(Spread))
          use _ <- do(nibble.token(Div))
          return("..")
        }),
      )
      use parts <- do(nibble.many1(nibble.one_of(path_valid)))
      let prefix = string.join(dots, "/")
      return(prefix <> "/" <> string.join(parts, ""))
    },
    // Absolute: /path
    {
      use parts <- do(nibble.many1(nibble.one_of(path_valid)))
      return("/" <> string.join(parts, ""))
    },
  ])
}

fn import_alias() -> Parser(String, Token, String) {
  use _ <- do(nibble.token(KwAs))
  var_name()
}

fn import_name() -> Parser(#(String, String), Token, String) {
  use name <- do(nibble.one_of([take_name(), op_name()]))
  use alias <- do(nibble.one_of([import_alias(), return(name)]))
  return(#(name, alias))
}

fn extern(file: String) -> Parser(Stmt, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwExtern))
    use name <- do(var_name())
    use _ <- do(nibble.token(LParen))
    use params <- do(nibble.sequence(expr(file), nibble.token(Comma)))
    use _ <- do(nibble.token(RParen))
    use _ <- do(nibble.token(ThinArrow))
    use returns <- do(expr(file))
    use end <- do(get_span(file))
    return(tao.extern(name, params, returns, merge(start, end)))
  }
  |> nibble.in("extern declaration")
}

fn let_var(file: String) -> Parser(Stmt, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwLet))
    use name <- do(let_name())
    use typ <- do(
      nibble.optional({
        use _ <- do(nibble.token(Colon))
        expr(file)
      }),
    )
    use _ <- do(nibble.token(Equals))
    use val <- do(expr(file))
    use end <- do(get_span(file))
    return(tao.let_var(name, typ, val, merge(start, end)))
  }
  |> nibble.in("let binding")
}

fn let_pat(file: String) -> Parser(Stmt, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwLet))
    use pat <- do(pattern(file))
    let types = []
    use _ <- do(nibble.token(Equals))
    use val <- do(expr(file))
    use end <- do(get_span(file))
    return(tao.let_pat(pat, types, val, merge(start, end)))
  }
  |> nibble.in("let binding")
}

fn fn_def(file: String) -> Parser(Stmt, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwFn))
    use name <- do(var_name())
    nibble.one_of([
      fn_def_body(file, start, name),
      fn_overload(file, start, name),
    ])
  }
  |> nibble.in("function definition")
}

fn parameters(file: String) -> Parser(Parameters, Token, String) {
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
  use opt_tail <- do(
    nibble.optional({
      use _ <- do(nibble.token(Comma))
      use _ <- do(nibble.token(Spread))
      use span <- do(get_span(file))
      nibble.one_of([expr(file), return(tao.hole_open(None, span))])
    }),
  )
  return(#(params, opt_tail))
}

fn fn_def_body(
  file: String,
  start: Span,
  name: String,
) -> Parser(Stmt, Token, String) {
  {
    use implicits <- do(nibble.optional(fn_implicits(file)))
    let implicits = option.unwrap(implicits, [])
    use _ <- do(nibble.token(LParen))
    use params <- do(parameters(file))
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
        use mod_name <- do(
          nibble.optional({
            use mod_name <- do(var_name())
            use _ <- do(nibble.token(Dot))
            return(mod_name)
          }),
        )
        use name <- do(var_name())
        use _ <- do(nibble.token(LParen))
        use args <- do(arguments(file, pattern(file)))
        use _ <- do(nibble.token(RParen))
        use opt_guard <- do(nibble.optional(guard(file)))
        use end <- do(get_span(file))
        let s = merge(start, end)
        return(tao.OverloadChoice(mod_name, name, args, opt_guard, s))
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
    return(tao.test_(">>> " <> name, exp, pat, merge(start, end)))
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
    punderscore(file),
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
  use name <- do(var_name())
  use end <- do(get_span(file))
  return(tao.pvar(name, merge(start, end)))
}

/// `_` (and `_N`) in a pattern position is a wildcard. `_` is now a
/// `Placeholder` token (not a name), so it is matched here, not in `pvar`.
fn punderscore(file: String) -> Parser(Pattern, Token, String) {
  use start <- do(get_span(file))
  use _n <- do(take_placeholder())
  use end <- do(get_span(file))
  return(tao.pany(merge(start, end)))
}

fn pctr(file: String) -> Parser(Pattern, Token, String) {
  use start <- do(get_span(file))
  use name <- do(take_tag())
  use opt_args <- do(
    nibble.optional({
      use _ <- do(nibble.token(LParen))
      use args <- do(arguments(file, pattern(file)))
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
      // Precedence (low to high): or < and < is/in < +,- < *,/
      pratt.infix_left(1, nibble.token(Or), op2(tao.Or)),
      pratt.infix_left(2, nibble.token(And), op2(tao.And)),
      pratt.infix_left(3, nibble.token(Is), op2(tao.Is)),
      pratt.infix_left(3, nibble.token(In), op2(tao.In)),
      pratt.infix_left(4, nibble.token(Add), op2(tao.Add)),
      pratt.infix_left(4, nibble.token(Sub), op2(tao.Sub)),
      pratt.infix_left(5, nibble.token(Mul), op2(tao.Mul)),
      pratt.infix_left(5, nibble.token(Div), op2(tao.Div)),
    ],
    dropping: return(Nil),
  )
  |> nibble.map(desugar_placeholders)
  |> nibble.in("expression")
}

fn atom(file: String) -> Parser(Expr, Token, String) {
  use base <- do(
    nibble.one_of([
      fn_expr(file),
      paren(file),
      placeholder(file),
      hole(file),
      float(file),
      int(file),
      var(file),
      ctr(file),
    ]),
  )
  postfix(file, base)
}

/// A `fn` expression: an anonymous function (`fn(x: a) = body`) or a
/// function type (`fn(x: a) -> b`). The two are disambiguated by the body:
/// a `=`/`{` makes it a function, a `->` without a body a type. Without an
/// annotation an unparenthesized parameter is a name (pattern) in the
/// function and a type in the type, so the function is tried first and the
/// type only when no body follows. `fn_value` is backtrackable: it can fail
/// after consuming tokens (e.g. `fn(a) -> b` has no body), and the failure
/// must not commit so that `fn_type` can re-read the same input.
fn fn_expr(file: String) -> Parser(Expr, Token, String) {
  nibble.one_of([nibble.backtrackable(fn_value(file)), fn_type(file)])
}

/// An anonymous function: `fn<implicits>(params) -> ret = body` or
/// `fn<implicits>(params) { stmts }`. The `-> ret` part is optional.
fn fn_value(file: String) -> Parser(Expr, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwFn))
    use implicits <- do(nibble.optional(fn_implicits(file)))
    let implicits = option.unwrap(implicits, [])
    use _ <- do(nibble.token(LParen))
    use params <- do(parameters(file))
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
          use _ <- do(nibble.token(Equals))
          expr(file)
        },
        {
          use _ <- do(nibble.token(LBrace))
          use stmts <- do(nibble.many(stmt(file)))
          use _ <- do(nibble.token(RBrace))
          return(tao.do(stmts, start))
        },
      ]),
    )
    use end <- do(get_span(file))
    return(tao.Expr(
      tao.Fn(None, implicits, params, opt_return, body),
      merge(start, end),
    ))
  }
  |> nibble.in("anonymous function")
}

/// A function *type*: `fn<implicits>(params) -> returns`.
fn fn_type(file: String) -> Parser(Expr, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwFn))
    use implicits <- do(nibble.optional(fn_implicits(file)))
    let implicits = option.unwrap(implicits, [])
    use _ <- do(nibble.token(LParen))
    use params <- do(sequence(fn_type_param(file), Comma))
    use _ <- do(nibble.token(RParen))
    use _ <- do(nibble.token(ThinArrow))
    use ret <- do(expr(file))
    use end <- do(get_span(file))
    return(tao.fn_t(implicits, #(params, None), ret, merge(start, end)))
  }
  |> nibble.in("function type")
}

/// Implicit (quantified) parameters: `<a, b: Type>` — names with optional
/// type annotations (no patterns, no defaults).
fn fn_implicits(file: String) -> Parser(tao.Implicits, Token, String) {
  use _ <- do(nibble.token(LAngle))
  use params <- do(sequence(type_parameter(file), Comma))
  use _ <- do(nibble.token(RAngle))
  return(params)
}

/// One parameter of a function type: a type, optionally named (`x: a` binds
/// `x` so the return type may depend on it).
fn fn_type_param(file: String) -> Parser(tao.Param, Token, String) {
  use opt_named <- do(
    nibble.optional({
      use nstart <- do(get_span(file))
      use name <- do(take_var())
      use nend <- do(get_span(file))
      use _ <- do(nibble.token(Colon))
      return(#(name, merge(nstart, nend)))
    }),
  )
  use typ <- do(expr(file))
  let pattern = case opt_named {
    Some(#(name, nspan)) -> tao.pvar(name, nspan)
    None -> tao.pany(typ.span)
  }
  return(#(pattern, #(Some(typ), None)))
}

/// A parenthesized expression: `(expr)`.
fn paren(file: String) -> Parser(Expr, Token, String) {
  use _ <- do(nibble.token(LParen))
  use e <- do(expr(file))
  use _ <- do(nibble.token(RParen))
  return(e)
}

/// Placeholder positions are capped: `_N` desugars to an N-parameter
/// function, so an unbounded N (e.g. `_99999999999999999999`) would build
/// an unbounded parameter list at parse time.
const max_placeholder_index = 100

/// A placeholder (`_` or `_N`): an anonymous-function argument. Desugared to a
/// `Fn` by `desugar_placeholders` after the enclosing expression is parsed.
fn placeholder(file: String) -> Parser(Expr, Token, String) {
  use start <- do(get_span(file))
  use n <- do(take_placeholder())
  use end <- do(get_span(file))
  let span = merge(start, end)
  case n {
    // `_` is the first argument.
    None -> return(tao.placeholder(1, span))
    // `_0` is not a valid position (positions are 1-based).
    Some(0) ->
      nibble.throw(
        "_0 is not a valid placeholder; positions are 1-based, so the first argument is _ (or _1)",
      )
    Some(n) if n > max_placeholder_index ->
      nibble.throw(
        "_" <> int.to_string(n)
        <> " is too large; placeholder positions are capped at "
        <> int.to_string(max_placeholder_index),
      )
    Some(n) -> return(tao.placeholder(n, span))
  }
}

fn take_placeholder() -> Parser(Option(Int), Token, String) {
  nibble.take_map("a placeholder", fn(tok) {
    case tok {
      Placeholder(n) -> Some(n)
      _ -> None
    }
  })
}

// ============================================================================
// PLACEHOLDER DESUGARING
//
// A placeholder (`_`, `_N`) is an anonymous-function argument. After an
// expression is parsed, `desugar_placeholders` collects every placeholder
// index in it; if there is at least one, the whole expression is wrapped in an
// anonymous `Fn` whose parameters are the placeholders (1-indexed, `_` is
// sugar for `_1`), and each placeholder is replaced by the corresponding
// parameter variable. E.g. `_ + 1` -> `fn(x1) = x1 + 1`, `_2 < _1` ->
// `fn(x1, x2) = x2 < x1`.
//
// Only the pratt *spine* of the expression is walked: every sub-expression
// (application args, match cases, fn bodies, ...) was parsed — and already
// desugared — by its own `expr` call, so it contains no raw placeholders.
// The spine is what this parse level built itself: atoms, `Op1`/`Op2`
// operands, the fun of an `App`, the base of a `Dot`.
// ============================================================================

fn ph_name(index: Int) -> String {
  "__ph" <> int.to_string(index)
}

fn desugar_placeholders(e: Expr) -> Expr {
  let #(indices, body) = ph_spine(e, [])
  case indices {
    [] -> e
    [_, ..] -> {
      let num = ph_max(indices)
      let params = ph_params(num, e.span)
      tao.Expr(tao.Fn(None, [], #(params, None), None, body), e.span)
    }
  }
}

fn ph_max(indices: List(Int)) -> Int {
  list.fold(indices, 0, fn(acc, n) { int.max(acc, n) })
}

fn ph_params(num: Int, span: Span) -> List(tao.Param) {
  int_range(1, num)
  |> list.map(fn(i) { #(tao.pvar(ph_name(i), span), #(None, None)) })
}

fn int_range(from: Int, to: Int) -> List(Int) {
  case from > to {
    True -> []
    False -> [from, ..int_range(from + 1, to)]
  }
}

/// Walk the pratt spine, replacing every `Placeholder(n)` with the variable
/// `__ph<n>` and collecting the indices that were present (threaded through
/// `acc`). Non-spine children are already placeholder-free.
fn ph_spine(e: Expr, acc: List(Int)) -> #(List(Int), Expr) {
  case e.data {
    tao.Placeholder(n) -> #([n, ..acc], tao.var(ph_name(n), e.span))
    tao.Op1(op, x) -> {
      let #(i, new_x) = ph_spine(x, acc)
      #(i, tao.Expr(tao.Op1(op, new_x), e.span))
    }
    tao.Op2(op, lhs, rhs) -> {
      let #(i1, new_lhs) = ph_spine(lhs, acc)
      let #(i2, new_rhs) = ph_spine(rhs, i1)
      #(i2, tao.Expr(tao.Op2(op, new_lhs, new_rhs), e.span))
    }
    tao.App(fun, args, tail) -> {
      let #(i, new_fun) = ph_spine(fun, acc)
      #(i, tao.Expr(tao.App(new_fun, args, tail), e.span))
    }
    tao.Dot(base, field) -> {
      let #(i, new_base) = ph_spine(base, acc)
      #(i, tao.Expr(tao.Dot(new_base, field), e.span))
    }
    _ -> #(acc, e)
  }
}

/// Postfix operators on an atom: field access `expr.field` (e.g.
/// `bool._and` on a module record — a module is a record of its
/// definitions, so access desugars to a field match) and application
/// `expr(...)`. They chain left-associatively (`a.b.c`, `f(x).field`).
fn postfix(file: String, expr: Expr) -> Parser(Expr, Token, String) {
  nibble.one_of([
    {
      use start <- do(get_span(file))
      use _ <- do(nibble.token(Dot))
      use field <- do(take_name())
      use end <- do(get_span(file))
      postfix(file, tao.dot(expr, field, merge(start, end)))
    },
    {
      use e <- do(app(file, expr))
      postfix(file, e)
    },
    return(expr),
  ])
}

fn hole(file: String) -> Parser(Expr, Token, String) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(Question))
  use end <- do(get_span(file))
  return(tao.hole_open(None, merge(start, end)))
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

fn var_name() -> Parser(String, Token, String) {
  nibble.one_of([take_var(), op_name()])
}

/// A `let` name: a variable name, a parenthesized operator, or a
/// placeholder. `_` is a `Placeholder` token (not a name), so a wildcard
/// binding (`let _ = ...`) is accepted here and kept under the name `"_"`.
fn let_name() -> Parser(String, Token, String) {
  nibble.one_of([
    var_name(),
    {
      use _ <- do(take_placeholder())
      return("_")
    },
  ])
}

/// A parenthesized operator name: `(*)`, `(and)`, ... — operators are
/// keywords/symbols, so naming them requires the parentheses.
fn op_name() -> Parser(String, Token, String) {
  let ops = [Add, Sub, Mul, Div, And, Or, Is, In]
  let ops_names = list.map(ops, token_text)
  use _ <- do(nibble.token(LParen))
  use name <- do(nibble.one_of(ops_names))
  use _ <- do(nibble.token(RParen))
  return(name)
}

fn var(file: String) -> Parser(Expr, Token, String) {
  use start <- do(get_span(file))
  use name <- do(var_name())
  use end <- do(get_span(file))
  return(tao.var(name, merge(start, end)))
}

fn ctr(file: String) -> Parser(Expr, Token, String) {
  use start <- do(get_span(file))
  use name <- do(take_tag())
  use opt_args <- do(
    nibble.optional({
      use _ <- do(nibble.token(LParen))
      use args <- do(arguments(file, expr(file)))
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
  use args <- do(arguments(file, expr(file)))
  use _ <- do(nibble.token(RParen))
  use end <- do(get_span(file))
  return(tao.app(fun, args, merge(start, end)))
}

/// `match a { ... }` — a comma-separated argument list is tuple sugar:
/// `match a, b { ... }` parses as `match (a, b) { ... }`, where
/// `(a, b)` is a single `Tuple` expression.
fn match(file: String) -> Parser(Expr, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(KwMatch))
    use args <- do(nibble.sequence(expr(file), nibble.token(Comma)))
    use _ <- do(nibble.token(LBrace))
    use cases <- do(nibble.many(match_case(file)))
    use _ <- do(nibble.token(RBrace))
    use end <- do(get_span(file))
    let arg = case args {
      [] -> tao.err(start)
      // Unreachable: `sequence` requires one or more
      [arg] -> arg
      [first, ..rest] -> {
        let last = case rest {
          [] -> first
          [second, ..] -> list.last(rest) |> result.unwrap(second)
        }
        tao.tuple(args, merge(first.span, last.span))
      }
    }
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
            tao.hole_open(None, merge(start, start)),
          )
        return(tao.match(cond, [true_case, false_case], merge(start, end)))
      }
    }
  }
  |> nibble.in("if expression")
}

/// `| p => ...` — a comma-separated pattern list is tuple sugar:
/// `| p1, p2 => ...` parses as `| (p1, p2) => ...`, where `(p1, p2)`
/// is a single `PTuple` pattern.
fn match_case(file: String) -> Parser(Case, Token, String) {
  {
    use start <- do(get_span(file))
    use _ <- do(nibble.token(Pipe))
    use pats <- do(nibble.sequence(pattern(file), nibble.token(Comma)))
    use opt_guard <- do(nibble.optional(guard(file)))
    use _ <- do(nibble.token(FatArrow))
    use body <- do(expr(file))
    let pat = case pats {
      [] -> tao.pany(start)
      // Unreachable: `sequence` requires one or more
      [pat] -> pat
      [first, ..rest] -> {
        let last = case rest {
          [] -> first
          [second, ..] -> list.last(rest) |> result.unwrap(second)
        }
        tao.ptuple(pats, merge(first.span, last.span))
      }
    }
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

fn token_text(tok: Token) -> Parser(String, Token, String) {
  use _ <- do(nibble.token(tok))
  return(token_to_string(tok))
}

fn take_name() -> Parser(String, Token, String) {
  nibble.take_map("a name", fn(tok) {
    case tok {
      Name("_") -> Some("_")
      Name(name) -> Some(name)
      _ -> None
    }
  })
}

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

fn sequence(
  item: Parser(a, Token, String),
  delim: Token,
) -> Parser(List(a), Token, String) {
  use items <- do(nibble.sequence(item, nibble.token(delim)))
  use _ <- do(nibble.optional(nibble.token(delim)))
  return(items)
}

fn arguments(
  _file: String,
  item: Parser(a, Token, String),
) -> Parser(List(#(String, a)), Token, String) {
  let arg_parser = {
    use opt_name <- do(
      nibble.optional({
        use name <- do(var_name())
        use _ <- do(nibble.token(Colon))
        return(name)
      }),
    )
    use arg <- do(item)
    return(#(option.unwrap(opt_name, ""), arg))
  }
  sequence(arg_parser, Comma)
}

// ============================================================================
// HELPERS
// ============================================================================

fn get_span(file: String) -> Parser(Span, Token, String) {
  use s <- do(nibble.span())
  return(Span(file, s.row_start, s.col_start, s.row_end, s.col_end))
}

/// Tags are identifiers whose first non-`_` grapheme is uppercase.
fn is_tag_name(name: String) -> Bool {
  case string.pop_grapheme(name) {
    Ok(#("_", rest)) -> is_tag_name(rest)
    Ok(#(first, _)) -> first != "" && first == string.uppercase(first)
    _ -> False
  }
}
