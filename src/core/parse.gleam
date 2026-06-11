/// Core Language Parser
///
/// Parses Core source text into AST using the nibble parser combinator library.
import core/ast.{
  type AST, type Case, type Pattern, type TypeDefinition, type Variant,
}
import core/error.{type Error} as e
import core/literals.{type LiteralType} as lit
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/regexp
import gleam/result.{try}
import gleam/set.{type Set}
import gleam/string
import nibble.{type Parser, do, return}
import nibble/lexer.{
  type Error as LexError, type Lexer, type Matcher, type Span as LexSpan,
  type Token as LexToken, NoMatchFound,
}
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
) -> Result(List(LexToken(Token)), Error) {
  case lexer.run(source, core_lexer()) {
    Ok(tokens) -> Ok(tokens)
    Error(lexer.NoMatchFound(row, col, lexeme)) ->
      Error(e.UnexpectedToken(lexeme, Span(file, row, col, row, col)))
  }
}

pub fn parse(file: String, source: String) -> Result(AST, Error) {
  use tokens <- try(lex(file, source))
  case nibble.run(tokens, term(file)) {
    Ok(ast) -> Ok(ast)
    Error(err) -> {
      echo err
      todo as "return an actual context.Error"
    }
  }
}

// ============================================================================
// LEXER
// ============================================================================

fn core_lexer() -> Lexer(Token, Nil) {
  lexer.simple([
    // Keywords with % prefix
    lexer.keyword("%Type", "[^\\w]", KwType),
    lexer.keyword("%Int", "[^\\w]", KwIntT),
    lexer.keyword("%Float", "[^\\w]", KwFloatT),
    lexer.keyword("%I8", "[^\\w]", KwI8),
    lexer.keyword("%I16", "[^\\w]", KwI16),
    lexer.keyword("%I32", "[^\\w]", KwI32),
    lexer.keyword("%I64", "[^\\w]", KwI64),
    lexer.keyword("%U8", "[^\\w]", KwU8),
    lexer.keyword("%U16", "[^\\w]", KwU16),
    lexer.keyword("%U32", "[^\\w]", KwU32),
    lexer.keyword("%U64", "[^\\w]", KwU64),
    lexer.keyword("%F16", "[^\\w]", KwF16),
    lexer.keyword("%F32", "[^\\w]", KwF32),
    lexer.keyword("%F64", "[^\\w]", KwF64),

    lexer.keyword("%fn", "[^\\w]", KwFn),
    lexer.keyword("%pi", "[^\\w]", KwPi),
    lexer.keyword("%let", "[^\\w]", KwLet),
    lexer.keyword("%match", "[^\\w]", KwMatch),
    lexer.keyword("%fix", "[^\\w]", KwFix),
    lexer.keyword("%error", "[^\\w]", KwError),

    // Names
    lexer.identifier("[_a-zA-Z]", "[_a-zA-Z0-9]", set.new(), Name),

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
    lexer.token("=", Equals),
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

fn term(file: String) -> Parser(AST, Token, Nil) {
  nibble.one_of([
    typ(file),
    hole(file),
    int(file),
    float(file),
    lit_type(file),
    var(file),
    tag(file),
    rcd(file),
    // lambda_expr(file),
  // pi_expr(file),
  // let_expr(file),
  // fix_expr(file),
  // match_expr(file),
  // error_expr(file),
  // builtin_call(file),
  // record_type_expr(file),
  // paren_expr(file),
  // paren_ann_expr(file),
  ])
}

fn typ(file: String) -> Parser(AST, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(KwType))
  use universe <- do(
    nibble.one_of([
      angle_brackets(take_int()),
      nibble.return(0),
    ]),
  )
  use end <- do(get_span(file))
  return(ast.typ(universe, span.merge(start, end)))
}

fn hole(file: String) -> Parser(AST, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(Question))
  use id <- do(
    nibble.one_of([
      angle_brackets(take_int()),
      nibble.return(-1),
    ]),
  )
  use end <- do(get_span(file))
  return(ast.hole(id, span.merge(start, end)))
}

fn int(file: String) -> Parser(AST, Token, Nil) {
  use start <- do(get_span(file))
  use n <- do(take_int())
  use end <- do(get_span(file))
  return(ast.int(n, span.merge(start, end)))
}

fn float(file: String) -> Parser(AST, Token, Nil) {
  use start <- do(get_span(file))
  use num <- do(take_float())
  use end <- do(get_span(file))
  return(ast.float(num, span.merge(start, end)))
}

fn lit_type(file: String) -> Parser(AST, Token, Nil) {
  use start <- do(get_span(file))
  use type_ <- do(take_lit_type())
  use end <- do(get_span(file))
  return(ast.AST(ast.LitT(type_), span.merge(start, end)))
}

fn var(file: String) -> Parser(AST, Token, Nil) {
  use start <- do(get_span(file))
  use name <- do(take_ident())
  use end <- do(get_span(file))
  return(ast.var(name, span.merge(start, end)))
}

fn tag(file: String) -> Parser(AST, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(Hash))
  use tag <- do(take_ident())
  use _ <- do(nibble.token(LParen))
  use arg <- do(term(file))
  use _ <- do(nibble.token(RParen))
  use end <- do(get_span(file))
  return(ast.AST(ast.Ctr(tag, arg), span.merge(start, end)))
}

fn rcd(file: String) -> Parser(AST, Token, Nil) {
  use start <- do(get_span(file))
  use _ <- do(nibble.token(LBrace))
  use fields <- do(
    nibble.one_of([
      comma_separated({
        use name <- do(take_ident())
        use _ <- do(nibble.token(Colon))
        use value <- do(term(file))
        return(#(name, value))
      }),
      nibble.return([]),
    ]),
  )
  use _ <- do(nibble.token(RBrace))
  use end <- do(get_span(file))
  return(ast.rcd(fields, span.merge(start, end)))
}

// fn lambda_expr(file: String) -> Parser(AST, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(KwFn))
//   // Optional implicit params: <a: Type, b: Type>
//   use implicits <- do(
//     nibble.one_of([implicit_param_list(file), nibble.return([])]),
//   )
//   // (param_name: param_type) or (param_type) — sugar
//   use _ <- do(nibble.token(LParen))
//   use param <- do(
//     nibble.one_of([
//       // Named: (x: Type)
//       {
//         use name <- do(take_ident())
//         use _ <- do(nibble.token(Colon))
//         use typ <- do(expression(file))
//         return(#(name, typ))
//       },
//       // Sugar: (Type) — anonymous, equivalent to (_: Type)
//       {
//         use typ <- do(expression(file))
//         return(#("_", typ))
//       },
//     ]),
//   )
//   use _ <- do(nibble.token(RParen))
//   // => body
//   use _ <- do(nibble.token(FatArrow))
//   use body <- do(expression(file))
//   use end <- do(get_span(file))

//   let lam = AST(core.ast.Lam(False, param, body), span.merge(start, end))
//   let lam =
//     list.fold(implicits, lam, fn(acc, imp) {
//       let #(name, typ) = imp
//       AST(core.ast.Lam(True, #(name, typ), acc), span.merge(start, end))
//     })
//   return(lam)
// }

// fn pi_expr(file: String) -> Parser(AST, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(KwPi))
//   // Optional implicit params: <a: Type, b: Type>
//   use implicits <- do(
//     nibble.one_of([implicit_param_list(file), nibble.return([])]),
//   )
//   // (domain_name: domain_type) or (domain_type) — sugar
//   use _ <- do(nibble.token(LParen))
//   use domain <- do(
//     nibble.one_of([
//       // Named: (x: Type)
//       {
//         use name <- do(take_ident())
//         use _ <- do(nibble.token(Colon))
//         use typ <- do(expression(file))
//         return(#(name, typ))
//       },
//       // Sugar: (Type) — anonymous
//       {
//         use typ <- do(expression(file))
//         return(#("_", typ))
//       },
//     ]),
//   )
//   use _ <- do(nibble.token(RParen))
//   // -> codomain
//   use _ <- do(nibble.token(ThinArrow))
//   use codomain <- do(expression(file))
//   use end <- do(get_span(file))

//   let pi = AST(core.ast.Pi(False, domain, codomain), span.merge(start, end))
//   let pi =
//     list.fold(implicits, pi, fn(acc, imp) {
//       let #(name, typ) = imp
//       AST(core.ast.Pi(True, #(name, typ), acc), span.merge(start, end))
//     })
//   return(pi)
// }

// fn let_expr(file: String) -> Parser(AST, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(KwLet))
//   use name <- do(take_ident())
//   use param_type <- do(
//     nibble.one_of([
//       // %let name: Type = value
//       {
//         use _ <- do(nibble.token(Colon))
//         use typ <- do(expression(file))
//         return(typ)
//       },
//       // %let name = value (hole type)
//       {
//         use s <- do(get_span(file))
//         return(AST(core.ast.Hole(-1), s))
//       },
//     ]),
//   )
//   use _ <- do(nibble.token(Equals))
//   use value <- do(expression(file))
//   use end <- do(get_span(file))

//   // %let desugars to: (%fn(name: Type) => body) value
//   // The "body" is the rest of the expression, captured via Hole
//   return(AST(
//     core.ast.Let(name, param_type, value, AST(core.ast.Hole(-1), end)),
//     span.merge(start, end),
//   ))
// }

// fn fix_expr(file: String) -> Parser(AST, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(KwFix))
//   use name <- do(take_ident())
//   use _ <- do(nibble.token(Dot))
//   use body <- do(expression(file))
//   use end <- do(get_span(file))
//   return(AST(core.ast.Fix(name, body), span.merge(start, end)))
// }

// fn match_expr(file: String) -> Parser(AST, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(KwMatch))
//   // (arg)
//   use _ <- do(nibble.token(LParen))
//   use arg <- do(expression(file))
//   use _ <- do(nibble.token(RParen))
//   // { | case | case }
//   use _ <- do(nibble.token(LBrace))
//   use cases <- do(nibble.many(match_case(file)))
//   use _ <- do(nibble.token(RBrace))
//   use end <- do(get_span(file))
//   return(AST(core.ast.Match(arg, cases), span.merge(start, end)))
// }

// fn error_expr(file: String) -> Parser(AST, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(KwError))
//   // Optional string message
//   use _ <- do(
//     nibble.one_of([
//       {
//         use _ <- do(take_str())
//         return(Nil)
//       },
//       nibble.return(Nil),
//     ]),
//   )
//   use end <- do(get_span(file))
//   return(AST(core.ast.Err, span.merge(start, end)))
// }

// fn builtin_call(file: String) -> Parser(AST, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(At))
//   use name <- do(take_ident())
//   // <ReturnType>
//   use _ <- do(nibble.token(LAngle))
//   use return_type <- do(expression(file))
//   use _ <- do(nibble.token(RAngle))
//   // (arg1, arg2, ...)
//   use _ <- do(nibble.token(LParen))
//   use args <- do(
//     nibble.one_of([
//       comma_separated(file, annotated_arg(file)),
//       nibble.return([]),
//     ]),
//   )
//   use _ <- do(nibble.token(RParen))
//   use end <- do(get_span(file))
//   return(AST(core.ast.Call(name, args, return_type), span.merge(start, end)))
// }

// fn annotated_arg(file: String) -> Parser(AST, Token, Nil) {
//   use arg <- do(expression(file))
//   use _ <- do(nibble.token(Colon))
//   use _ <- do(expression(file))
//   return(arg)
// }

// fn record_type_expr(file: String) -> Parser(AST, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(Hash))
//   use _ <- do(nibble.token(LBrace))
//   use fields <- do(
//     nibble.one_of([
//       comma_separated(file, rcd_type_field(file)),
//       nibble.return([]),
//     ]),
//   )
//   use _ <- do(nibble.token(RBrace))
//   use end <- do(get_span(file))
//   return(AST(core.ast.RcdT(fields), span.merge(start, end)))
// }

// fn rcd_type_field(
//   file: String,
// ) -> Parser(#(String, #(AST, Option(AST))), Token, Nil) {
//   use name <- do(take_ident())
//   use _ <- do(nibble.token(Colon))
//   use typ <- do(expression(file))
//   use default <- do(
//     nibble.one_of([
//       {
//         use _ <- do(nibble.token(Equals))
//         use val <- do(expression(file))
//         return(Some(val))
//       },
//       nibble.return(None),
//     ]),
//   )
//   return(#(name, #(typ, default)))
// }

// fn paren_expr(file: String) -> Parser(AST, Token, Nil) {
//   use _ <- do(nibble.token(LParen))
//   use expr <- do(expression(file))
//   use _ <- do(nibble.token(RParen))
//   return(expr)
// }

// fn paren_ann_expr(file: String) -> Parser(AST, Token, Nil) {
//   use _ <- do(nibble.token(LParen))
//   use expr <- do(expression(file))
//   use _ <- do(nibble.token(Colon))
//   use typ <- do(expression(file))
//   use _ <- do(nibble.token(RParen))
//   return(AST(core.ast.Ann(expr, typ), span.merge(expr.span, typ.span)))
// }

// // ============================================================================
// // IMPLICIT PARAM LIST
// // ============================================================================

// fn implicit_param_list(
//   file: String,
// ) -> Parser(List(#(String, AST)), Token, Nil) {
//   use _ <- do(nibble.token(LAngle))
//   use params <- do(comma_separated(file, implicit_param(file)))
//   use _ <- do(nibble.token(RAngle))
//   return(params)
// }

// fn implicit_param(file: String) -> Parser(#(String, AST), Token, Nil) {
//   use name <- do(take_ident())
//   use _ <- do(nibble.token(Colon))
//   use typ <- do(expression(file))
//   return(#(name, typ))
// }

// // ============================================================================
// // MATCH CASES
// // ============================================================================

// fn match_case(file: String) -> Parser(Case, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(Pipe))
//   use pattern <- do(pattern_(file))
//   // Optional guard: ? expr ~ pass_pattern
//   use guard <- do(
//     nibble.one_of([
//       {
//         use _ <- do(nibble.token(Question))
//         use guard_expr <- do(expression(file))
//         use _ <- do(nibble.token(Tilde))
//         use pass_pattern <- do(pattern_(file))
//         return(Some(#(guard_expr, pass_pattern)))
//       },
//       nibble.return(None),
//     ]),
//   )
//   use _ <- do(nibble.token(FatArrow))
//   use body <- do(expression(file))
//   use end <- do(get_span(file))
//   return(Case(pattern, guard, body, span.merge(start, end)))
// }

// // ============================================================================
// // PATTERN PARSER
// // ============================================================================

// fn pattern_(file: String) -> Parser(Pattern, Token, Nil) {
//   nibble.one_of([
//     alias_pattern(file),
//     type_pattern(file),
//     ctor_pattern(file),
//     rcd_type_pattern(file),
//     rcd_pattern(file),
//     error_pattern(file),
//     int_pattern(file),
//     float_pattern(file),
//     wildcard_pattern(file),
//   ])
// }

// fn alias_pattern(file: String) -> Parser(Pattern, Token, Nil) {
//   use start <- do(get_span(file))
//   use name <- do(take_ident())
//   use _ <- do(nibble.token(At))
//   use inner <- do(pattern_(file))
//   use end <- do(get_span(file))
//   return(PAlias(name, inner, span.merge(start, end)))
// }

// fn type_pattern(file: String) -> Parser(Pattern, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(KwType))
//   use result <- do(
//     nibble.one_of([
//       // %Type<n>
//       {
//         use _ <- do(nibble.token(LAngle))
//         use n <- do(take_int())
//         use _ <- do(nibble.token(RAngle))
//         use end <- do(get_span(file))
//         return(PTyp(n, span.merge(start, end)))
//       },
//       // %Type<name> — binds variable
//       {
//         use _ <- do(nibble.token(LAngle))
//         use name <- do(take_ident())
//         use _ <- do(nibble.token(RAngle))
//         use end <- do(get_span(file))
//         return(ast.PAlias(
//           name,
//           ast.PTyp(0, span.merge(start, end)),
//           span.merge(start, end),
//         ))
//       },
//       // %Type (implicit 0)
//       {
//         use end <- do(get_span(file))
//         return(ast.PTyp(0, span.merge(start, end)))
//       },
//     ]),
//   )
//   return(result)
// }

// fn ctor_pattern(file: String) -> Parser(Pattern, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(Hash))
//   use tag <- do(take_ident())
//   use _ <- do(nibble.token(LParen))
//   use inner <- do(pattern_(file))
//   use _ <- do(nibble.token(RParen))
//   use end <- do(get_span(file))
//   return(ast.PCtr(tag, inner, span.merge(start, end)))
// }

// fn rcd_type_pattern(file: String) -> Parser(Pattern, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(Hash))
//   use _ <- do(nibble.token(LBrace))
//   use fields <- do(
//     nibble.one_of([
//       comma_separated(file, rcd_pat_field(file)),
//       nibble.return([]),
//     ]),
//   )
//   use _ <- do(nibble.token(RBrace))
//   use end <- do(get_span(file))
//   return(ast.PRcd(fields, span.merge(start, end)))
// }

// fn rcd_pattern(file: String) -> Parser(Pattern, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(LBrace))
//   use fields <- do(
//     nibble.one_of([
//       comma_separated(file, rcd_pat_field(file)),
//       nibble.return([]),
//     ]),
//   )
//   use _ <- do(nibble.token(RBrace))
//   use end <- do(get_span(file))
//   return(ast.PRcd(fields, span.merge(start, end)))
// }

// fn rcd_pat_field(file: String) -> Parser(#(String, Pattern), Token, Nil) {
//   use name <- do(take_ident())
//   use value <- do(
//     nibble.one_of([
//       // name: pattern
//       {
//         use _ <- do(nibble.token(Colon))
//         use pat <- do(pattern_(file))
//         return(pat)
//       },
//       // name (sugar for name: name)
//       {
//         use s <- do(get_span(file))
//         return(ast.pvar(name, s))
//       },
//     ]),
//   )
//   return(#(name, value))
// }

// fn error_pattern(file: String) -> Parser(Pattern, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(KwError))
//   use end <- do(get_span(file))
//   return(ast.PErr(span.merge(start, end)))
// }

// fn int_pattern(file: String) -> Parser(Pattern, Token, Nil) {
//   use start <- do(get_span(file))
//   use n <- do(take_int())
//   use end <- do(get_span(file))
//   return(ast.PLit(lit.Int(n), span.merge(start, end)))
// }

// fn float_pattern(file: String) -> Parser(Pattern, Token, Nil) {
//   use start <- do(get_span(file))
//   use f <- do(take_float())
//   use end <- do(get_span(file))
//   return(ast.PLit(lit.Float(f), span.merge(start, end)))
// }

// fn wildcard_pattern(file: String) -> Parser(Pattern, Token, Nil) {
//   use start <- do(get_span(file))
//   use _ <- do(nibble.token(At))
//   use end <- do(get_span(file))
//   return(ast.PAny(span.merge(start, end)))
// }

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
