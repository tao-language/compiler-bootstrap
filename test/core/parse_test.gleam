/// Tests for the Core language parser.
import core/ast.{type AST, type Case, type Data, type Pattern}
import core/error.{type Error} as e
import core/literals.{type Literal, type LiteralType} as lit
import core/parse as p
import gleam/list
import gleam/option.{None, Some}
import gleam/result.{try}
import gleam/string
import gleeunit
import syntax/span.{type Span, Span}

pub fn main() {
  gleeunit.main()
}

const filename = "parse_test"

fn s(r1: Int, c1: Int, r2: Int, c2: Int) -> Span {
  Span(filename, r1, c1, r2, c2)
}

fn lex(source: String) -> Result(List(p.Token), Error) {
  use tokens <- try(p.lex(filename, source))
  Ok(list.map(tokens, fn(tok) { tok.value }))
}

fn parse(source: String) -> Result(AST, Error) {
  p.parse(filename, source)
}

// ============================================================================
// Typ
// ============================================================================
pub fn lex_typ_test() {
  assert lex("%Type") == Ok([p.KwType])
  assert lex("%Type<42>") == Ok([p.KwType, p.LAngle, p.IntLit(42), p.RAngle])
  assert lex("%Type < 42 > ")
    == Ok([p.KwType, p.LAngle, p.IntLit(42), p.RAngle])
  assert lex("%Type\n<\n42\n>\n")
    == Ok([p.KwType, p.LAngle, p.IntLit(42), p.RAngle])
  assert lex("%Types ") == Error(e.UnexpectedToken("%Types ", s(1, 1, 1, 1)))
  assert lex("% Type ") == Error(e.UnexpectedToken("% Type ", s(1, 1, 1, 1)))
}

pub fn parse_typ_test() {
  assert parse("%Type") == Ok(ast.typ(0, s(1, 1, 1, 6)))
  assert parse("%Type<42>") == Ok(ast.typ(42, s(1, 1, 1, 10)))
}

// ============================================================================
// Hole
// ============================================================================
pub fn lex_hole_test() {
  assert lex("?") == Ok([p.Question])
  assert lex("?<42>") == Ok([p.Question, p.LAngle, p.IntLit(42), p.RAngle])
  assert lex("? < 42 > ") == Ok([p.Question, p.LAngle, p.IntLit(42), p.RAngle])
}

pub fn parse_hole_test() {
  assert parse("?") == Ok(ast.hole(-1, s(1, 1, 1, 2)))
  assert parse("?<42>") == Ok(ast.hole(42, s(1, 1, 1, 6)))
}

// ============================================================================
// Lit
// ============================================================================
pub fn lex_lit_test() {
  assert lex("42") == Ok([p.IntLit(42)])
  assert lex("3.14") == Ok([p.FloatLit(3.14)])
  assert lex("3 . 14 ") == Ok([p.IntLit(3), p.Dot, p.IntLit(14)])
}

pub fn parse_lit_test() {
  assert parse("42") == Ok(ast.int(42, s(1, 1, 1, 3)))
  assert parse("3.14") == Ok(ast.float(3.14, s(1, 1, 1, 5)))
}

// ============================================================================
// LitT
// ============================================================================
pub fn lex_litt_test() {
  assert lex("%Int") == Ok([p.KwIntT])
  assert lex("%Float") == Ok([p.KwFloatT])
  assert lex("%I8") == Ok([p.KwI8])
  assert lex("%I16") == Ok([p.KwI16])
  assert lex("%I32") == Ok([p.KwI32])
  assert lex("%I64") == Ok([p.KwI64])
  assert lex("%U8") == Ok([p.KwU8])
  assert lex("%U16") == Ok([p.KwU16])
  assert lex("%U32") == Ok([p.KwU32])
  assert lex("%U64") == Ok([p.KwU64])
  assert lex("%F16") == Ok([p.KwF16])
  assert lex("%F32") == Ok([p.KwF32])
  assert lex("%F64") == Ok([p.KwF64])
}

pub fn parse_litt_test() {
  assert parse("%Int") == Ok(ast.int_t(s(1, 1, 1, 5)))
  assert parse("%Float") == Ok(ast.float_t(s(1, 1, 1, 7)))
  assert parse("%I8") == Ok(ast.i8(s(1, 1, 1, 4)))
  assert parse("%I16") == Ok(ast.i16(s(1, 1, 1, 5)))
  assert parse("%I32") == Ok(ast.i32(s(1, 1, 1, 5)))
  assert parse("%I64") == Ok(ast.i64(s(1, 1, 1, 5)))
  assert parse("%U8") == Ok(ast.u8(s(1, 1, 1, 4)))
  assert parse("%U16") == Ok(ast.u16(s(1, 1, 1, 5)))
  assert parse("%U32") == Ok(ast.u32(s(1, 1, 1, 5)))
  assert parse("%U64") == Ok(ast.u64(s(1, 1, 1, 5)))
  assert parse("%F16") == Ok(ast.f16(s(1, 1, 1, 5)))
  assert parse("%F32") == Ok(ast.f32(s(1, 1, 1, 5)))
  assert parse("%F64") == Ok(ast.f64(s(1, 1, 1, 5)))
}

// ============================================================================
// Var
// ============================================================================
pub fn lex_var_test() {
  assert lex("x") == Ok([p.Name("x")])
  assert lex("xy") == Ok([p.Name("xy")])
  assert lex("xyz") == Ok([p.Name("xyz")])
  assert lex("XY") == Ok([p.Name("XY")])
  assert lex("x_") == Ok([p.Name("x_")])
  assert lex("_x") == Ok([p.Name("_x")])
  assert lex("x1") == Ok([p.Name("x1")])
  assert lex("1x") == Ok([p.IntLit(1), p.Name("x")])
  assert lex("_") == Ok([p.Name("_")])
}

pub fn parse_var_test() {
  assert parse("x") == Ok(ast.var("x", s(1, 1, 1, 2)))
}

// ============================================================================
// Ctr
// ============================================================================
pub fn lex_ctr_test() {
  assert lex("#A") == Ok([p.Hash, p.Name("A")])
  assert lex("#A(x)")
    == Ok([p.Hash, p.Name("A"), p.LParen, p.Name("x"), p.RParen])
  assert lex("# A ( x ) ")
    == Ok([p.Hash, p.Name("A"), p.LParen, p.Name("x"), p.RParen])
}

pub fn parse_ctr_test() {
  assert parse("#A(x)")
    == Ok(ast.AST(ast.Ctr("A", ast.var("x", s(1, 3, 1, 5))), s(1, 1, 1, 6)))
}

// ============================================================================
// Rcd
// ============================================================================
pub fn lex_rcd_test() {
  assert lex("{}") == Ok([p.LBrace, p.RBrace])
  assert lex("{a:x}")
    == Ok([p.LBrace, p.Name("a"), p.Colon, p.Name("x"), p.RBrace])
  assert lex("{ a : x } ")
    == Ok([p.LBrace, p.Name("a"), p.Colon, p.Name("x"), p.RBrace])
  assert lex("{a: x, b: y}")
    == Ok([
      p.LBrace,
      p.Name("a"),
      p.Colon,
      p.Name("x"),
      p.Comma,
      p.Name("b"),
      p.Colon,
      p.Name("y"),
      p.RBrace,
    ])
}

pub fn parse_rcd_test() {
  assert parse("{}") == Ok(ast.rcd([], s(1, 1, 1, 3)))
  assert parse("{a: x}")
    == Ok(ast.rcd([#("a", ast.var("x", s(1, 3, 1, 6)))], s(1, 1, 1, 7)))
}

// ============================================================================
// RcdT
// ============================================================================
pub fn lex_rcdt_test() {
  assert lex("%{}") == Ok([p.RcdTOpen, p.RBrace])
  assert lex("%{a:x=42}")
    == Ok([
      p.RcdTOpen,
      p.Name("a"),
      p.Colon,
      p.Name("x"),
      p.Equals,
      p.IntLit(42),
      p.RBrace,
    ])
  assert lex("%{ a : x = 42} ")
    == Ok([
      p.RcdTOpen,
      p.Name("a"),
      p.Colon,
      p.Name("x"),
      p.Equals,
      p.IntLit(42),
      p.RBrace,
    ])
  assert lex("%{a: x, b: y}")
    == Ok([
      p.RcdTOpen,
      p.Name("a"),
      p.Colon,
      p.Name("x"),
      p.Comma,
      p.Name("b"),
      p.Colon,
      p.Name("y"),
      p.RBrace,
    ])
}

pub fn parse_rcdt_test() {
  assert parse("%{}") == Ok(ast.rcd_t([], s(1, 1, 1, 4)))
  assert parse("%{a: x}")
    == Ok(ast.rcd_t(
      [#("a", #(ast.var("x", s(1, 4, 1, 7)), None))],
      s(1, 1, 1, 8),
    ))
  assert parse("%{a: x = 42}")
    == Ok(ast.rcd_t(
      [
        #(
          "a",
          #(ast.var("x", s(1, 4, 1, 7)), Some(ast.int(42, s(1, 8, 1, 12)))),
        ),
      ],
      s(1, 1, 1, 13),
    ))
}
// ============================================================================
// Ann
// ============================================================================
// pub fn parse_ann_test() { todo }
// ============================================================================
// Lam
// ============================================================================
// pub fn parse_lam_test() { todo }
// ============================================================================
// Pi
// ============================================================================
// pub fn parse_pi_test() { todo }
// ============================================================================
// Fix
// ============================================================================
// pub fn parse_fix_test() { todo }
// ============================================================================
// App
// ============================================================================
// pub fn parse_app_test() { todo }
// ============================================================================
// TypeDef
// ============================================================================
// pub fn parse_typedef_test() { todo }
// ============================================================================
// Let
// ============================================================================
// pub fn parse_let_test() { todo }
// ============================================================================
// Match
// ============================================================================
// pub fn parse_match_test() { todo }
// ============================================================================
// Call
// ============================================================================
// pub fn parse_call_test() { todo }
// ============================================================================
// Err
// ============================================================================
// pub fn parse_err_test() { todo }

// ============================================================================
// ERRORS
// ============================================================================

// pub fn parse_error_empty_test() { todo }
