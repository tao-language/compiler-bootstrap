// ============================================================================
// CORE LANGUAGE SYNTAX
// ============================================================================
/// Core language syntax with TypeScript-like surface syntax.
///
/// Supported terms:
/// - Variables: `x`
/// - Literals: `42`
/// - Lambda: `λx. body`
/// - Pi types: `(x : A) -> B`
/// - Application: `f(x)` (C-style only)
/// - Type annotations: `x : I32`
/// - Field access: `record.field`
/// - Records: `{x = 1, y = 2}`
/// - Constructors: `Some`, `True`, `False`, `None`
/// - Type universes: `Type0`, `Type1`, etc.
/// - Holes: `?` (unsolved metavariables)
/// - Literal types: `I32`, `I64`, `F64`
///
/// Both parser and formatter are derived from this single grammar definition.
import core/core.{
  type Term, Ann, App, Ctr, Dot, F32, F32T, F64, F64T, Hole, I32, I32T, I64, I64T, Lam, Lit,
  LitT, Pi, Rcd, Term, Typ, U32, U32T, U64, U64T, Var,
}
import gleam/float
import gleam/int
import gleam/list
import gleam/string
import syntax/formatter
import syntax/grammar.{type Span, AstValue, TokenValue}
import syntax/lexer.{type Token}

// ============================================================================
// PUBLIC API
// ============================================================================

pub fn parse(source: String) -> grammar.ParseResult(Term) {
  grammar.parse(core_grammar(), source)
}

pub fn format(term: Term) -> String {
  format_term(term, -1) |> formatter.render_default
}

// ============================================================================
// GRAMMAR DEFINITION
// ============================================================================

pub fn core_grammar() -> grammar.Grammar(Term) {
  use g <- grammar.define

  g
  |> grammar.name("Core")
  |> grammar.start("Expr")
  // Tokens
  |> grammar.token("Ident")
  |> grammar.token("Number")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.token("LBrace")
  |> grammar.token("RBrace")
  |> grammar.token("Lambda")
  |> grammar.token("Dot")
  |> grammar.token("Operator")
  |> grammar.token("Keyword")
  |> grammar.token("Colon")
  |> grammar.token("Equals")
  |> grammar.token("Comma")
  |> grammar.token("Arrow")
  // Main expression rule (lowest precedence first)
  |> grammar.rule("Expr", [
    grammar.alt(grammar.ref("Lambda"), unwrap, format_term),
    grammar.alt(grammar.ref("Pi"), unwrap, format_term),
    grammar.alt(grammar.ref("Ann"), unwrap, format_term),
    grammar.alt(grammar.ref("App"), unwrap, format_term),
    grammar.alt(grammar.ref("Dot"), unwrap, format_term),
    grammar.alt(grammar.ref("Atom"), unwrap, format_term),
  ])
  // Lambda: λx. body
  |> grammar.rule("Lambda", [
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Lambda"),
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Dot"),
        grammar.ref("Expr"),
      ]),
      make_lambda,
      format_term,
    ),
  ])
  // Pi type: (x : A) → B
  |> grammar.rule("Pi", [
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LParen"),
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Colon"),
        grammar.ref("Expr"),
        grammar.token_pattern("RParen"),
        grammar.token_pattern("Arrow"),
        grammar.ref("Expr"),
      ]),
      make_pi,
      format_term,
    ),
  ])
  // Type annotation: expr : Type
  |> grammar.rule("Ann", [
    grammar.alt(
      grammar.seq([
        grammar.ref("Atom"),
        grammar.token_pattern("Colon"),
        grammar.ref("Atom"),
      ]),
      make_annotation,
      format_term,
    ),
  ])
  // Application: f(x)
  |> grammar.rule("App", [
    grammar.alt(
      grammar.seq([
        grammar.ref("Atom"),
        grammar.token_pattern("LParen"),
        grammar.ref("Expr"),
        grammar.token_pattern("RParen"),
      ]),
      make_application,
      format_term,
    ),
  ])
  // Field access: expr.field
  |> grammar.rule("Dot", [
    grammar.alt(
      grammar.seq([
        grammar.ref("Atom"),
        grammar.token_pattern("Dot"),
        grammar.token_pattern("Ident"),
      ]),
      make_field_access,
      format_term,
    ),
  ])
  // Atoms - the building blocks
  |> grammar.rule("Atom", [
    // Record: {} (empty record for now)
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LBrace"),
        grammar.token_pattern("RBrace"),
      ]),
      make_empty_record,
      format_term,
    ),
    // Literal type: I32, I64, F64 (specific keywords)
    grammar.alt(grammar.token_pattern("Keyword"), make_literal_type_or_constructor, format_term),
    // Variable (identifiers that don't start with "Type")
    grammar.alt(grammar.token_pattern("Ident"), make_var_or_typ, format_term),
    // Number literal
    grammar.alt(grammar.token_pattern("Number"), make_literal, format_term),
    // Hole: ? (operator)
    grammar.alt(grammar.token_pattern("Operator"), make_hole, format_term),
    // Parenthesized expression
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LParen"),
        grammar.ref("Expr"),
        grammar.token_pattern("RParen"),
      ]),
      unwrap_parens,
      format_term,
    ),
  ])
}

// ============================================================================
// CONSTRUCTOR HELPERS
// ============================================================================

fn unwrap(values) {
  case values {
    [AstValue(term)] -> term
    _ -> panic as "Expected single Term value"
  }
}

fn unwrap_parens(values) {
  case values {
    [_, AstValue(term), _] -> term
    _ -> panic as "Expected (expr)"
  }
}

fn make_lambda(values) {
  case values {
    [TokenValue(lambda_token), TokenValue(name_token), _, AstValue(body)] ->
      Term(Lam(name_token.value, body), grammar.span_from_token(lambda_token, "input"))
    _ -> panic as "Expected lambda"
  }
}

fn make_application(values) {
  case values {
    [AstValue(fun), TokenValue(lparen_token), AstValue(arg), TokenValue(rparen_token)] ->
      Term(App(fun, arg), grammar.span_from_tokens(lparen_token, rparen_token, "input"))
    _ -> panic as "Expected f(args)"
  }
}

fn make_var(values) {
  case values {
    [TokenValue(token)] -> Term(Var(0), grammar.span_from_token(token, "input"))
    _ -> panic as "Expected identifier"
  }
}

fn make_var_or_typ(values) {
  case values {
    [TokenValue(token)] -> {
      // Check if it's a type universe (Type0, Type1, etc.)
      case string.starts_with(token.value, "Type") {
        True -> {
          let level_str = string.drop_start(token.value, 4)
          case int.parse(level_str) {
            Ok(level) -> Term(Typ(level), grammar.span_from_token(token, "input"))
            Error(_) -> Term(Typ(0), grammar.span_from_token(token, "input"))
          }
        }
        False -> Term(Var(0), grammar.span_from_token(token, "input"))
      }
    }
    _ -> panic as "Expected identifier"
  }
}

fn make_literal(values) {
  case values {
    [TokenValue(token)] -> {
      case int.parse(token.value) {
        Ok(n) -> Term(Lit(I32(n)), grammar.span_from_token(token, "input"))
        Error(_) -> Term(Lit(I32(0)), grammar.span_from_token(token, "input"))
      }
    }
    _ -> panic as "Expected number token"
  }
}

fn make_hole(values) {
  case values {
    [TokenValue(token)] -> {
      case token.value {
        "?" -> Term(Hole(0), grammar.span_from_token(token, "input"))
        _ -> panic as "Expected ? operator"
      }
    }
    _ -> panic as "Expected hole (?)"
  }
}

fn make_literal_type_or_constructor(values) {
  case values {
    [TokenValue(token)] -> {
      // Check if it's a literal type (I32, I64, etc.)
      case token.value {
        "I32" | "I64" | "F32" | "F64" | "U32" | "U64" -> {
          let typ = case token.value {
            "I32" -> I32T
            "I64" -> I64T
            "F32" -> F32T
            "F64" -> F64T
            "U32" -> U32T
            "U64" -> U64T
            _ -> I32T
          }
          Term(LitT(typ), grammar.span_from_token(token, "input"))
        }
        // Otherwise it's a constructor tag
        _ -> {
          let hole_span = grammar.span_from_token(token, "input")
          Term(Ctr(token.value, Term(Hole(0), hole_span)), hole_span)
        }
      }
    }
    _ -> panic as "Expected keyword"
  }
}

fn make_annotation(values) {
  case values {
    [AstValue(term), _, AstValue(typ)] ->
      Term(Ann(term, typ), term.span)
    _ -> panic as "Expected annotation (term : type)"
  }
}

fn make_pi(values) {
  case values {
    [_, TokenValue(name_token), _, AstValue(in_term), _, _, AstValue(out_term)] ->
      Term(Pi(name_token.value, in_term, out_term), in_term.span)
    _ -> panic as "Expected Pi type ((x : A) -> B)"
  }
}

fn make_field_access(values) {
  case values {
    [AstValue(arg), _, TokenValue(field_token)] ->
      Term(Dot(arg, field_token.value), arg.span)
    _ -> panic as "Expected field access (expr.field)"
  }
}

fn make_empty_record(values) {
  case values {
    [_, _] -> Term(Rcd([]), grammar.span_from_token(values |> get_first_token, "input"))
    _ -> panic as "Expected empty record {}"
  }
}

fn get_first_token(values: List(grammar.Value(Term))) -> Token {
  case values {
    [TokenValue(token), ..] -> token
    [AstValue(term), ..] -> {
      let t: Term = term
      t.span |> span_to_token
    }
    _ -> panic as "Expected at least one value"
  }
}

fn span_to_token(span: Span) -> Token {
  lexer.Token("Unknown", "", span.start_line, span.end_col, span.start_line, span.start_col)
}

// ============================================================================
// FORMATTER
// ============================================================================

fn format_term(term: Term, parent_prec: Int) -> formatter.Doc {
  case term.data {
    Var(index) ->
      formatter.concat([
        formatter.text("var"),
        formatter.text(int.to_string(index)),
      ])
    Lit(value) -> {
      case value {
        I32(n) -> formatter.text(int.to_string(n))
        I64(n) -> formatter.concat([formatter.text(int.to_string(n)), formatter.text("i64")])
        U32(n) -> formatter.concat([formatter.text(int.to_string(n)), formatter.text("u32")])
        U64(n) -> formatter.concat([formatter.text(int.to_string(n)), formatter.text("u64")])
        F32(f) -> formatter.text(float.to_string(f))
        F64(f) -> formatter.text(float.to_string(f))
      }
    }
    Typ(level) ->
      formatter.concat([
        formatter.text("Type"),
        formatter.text(int.to_string(level)),
      ])
    Hole(_) -> formatter.text("?")
    LitT(typ) -> {
      case typ {
        I32T -> formatter.text("I32")
        I64T -> formatter.text("I64")
        U32T -> formatter.text("U32")
        U64T -> formatter.text("U64")
        F32T -> formatter.text("F32")
        F64T -> formatter.text("F64")
      }
    }
    Ctr(tag, _) ->
      // Constructor with Hole arg - just show the tag
      formatter.text(tag)
    Dot(arg, field) -> {
      let inner =
        formatter.concat([
          format_term(arg, 90),
          formatter.text("."),
          formatter.text(field),
        ])
      wrap_parens(inner, 90 < parent_prec)
    }
    Ann(term, typ) -> {
      let inner =
        formatter.concat([
          format_term(term, 50),
          formatter.text(" : "),
          format_term(typ, 50),
        ])
      wrap_parens(inner, 50 < parent_prec)
    }
    Pi(name, in_term, out_term) -> {
      let inner =
        formatter.concat([
          formatter.text("("),
          formatter.text(name),
          formatter.text(" : "),
          format_term(in_term, 50),
          formatter.text(") → "),
          format_term(out_term, 65),
        ])
      wrap_parens(inner, 65 < parent_prec)
    }
    Rcd(fields) -> {
      case fields {
        [] -> formatter.text("{}")
        _ -> {
          let field_docs =
            fields
            |> list.map(fn(field) {
              let #(name, value) = field
              formatter.concat([
                formatter.text(name),
                formatter.text(" = "),
                format_term(value, 50),
              ])
            })
          formatter.concat([
            formatter.text("{"),
            list.intersperse(field_docs, formatter.text(", ")) |> formatter.concat,
            formatter.text("}"),
          ])
        }
      }
    }
    Lam(name, body) -> {
      let inner =
        formatter.concat([
          formatter.text("λ"),
          formatter.text(name),
          formatter.text(". "),
          format_term(body, 70),
        ])
      wrap_parens(inner, 70 < parent_prec)
    }
    App(fun, arg) -> {
      let inner =
        formatter.concat([
          format_term(fun, 85),
          formatter.text("("),
          format_term(arg, 85),
          formatter.text(")"),
        ])
      wrap_parens(inner, 85 < parent_prec)
    }
    _ -> formatter.text("<unknown>")
  }
}

fn wrap_parens(doc, condition) {
  case condition {
    True -> formatter.parens(doc)
    False -> doc
  }
}
