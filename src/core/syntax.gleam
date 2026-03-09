// ============================================================================
// CORE LANGUAGE SYNTAX
// ============================================================================
/// Core language syntax with TypeScript-like surface syntax.
///
/// Supported terms:
/// - Variables: `x`
/// - Literals: `42`
/// - Lambda: `x -> body`
/// - Pi types: `(x : A) -> B`
/// - Application: `f(x)` (C-style only)
/// - Type annotations: `x : $I32`
/// - Field access: `record.field`
/// - Records: `{}`, `{x: 1}`, `{x: 1, y: 2}`
/// - Constructors: `#True`, `#Some`, `#Maybe(a)`
/// - Type universes: `$Type`, `$Type(1)`, `$Type(2)`
/// - Holes: `?`, `?1`, `?2` (unsolved metavariables)
/// - Literal types: `$I32`, `$I64`, `$F64`
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
  format_term(term, -1, []) |> formatter.render_default
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
  |> grammar.token("Dot")
  |> grammar.token("Operator")
  |> grammar.token("Keyword")
  |> grammar.token("Colon")
  |> grammar.token("Equals")
  |> grammar.token("Comma")
  |> grammar.token("Arrow")
  |> grammar.token("Dollar")
  |> grammar.token("Hash")
  |> grammar.token("Question")
  // Main expression rule (lowest precedence first)
  |> grammar.rule("Expr", [
    grammar.alt(grammar.ref("Lambda"), unwrap, fn(t, p) { format_term(t, p, []) }),
    grammar.alt(grammar.ref("Pi"), unwrap, fn(t, p) { format_term(t, p, []) }),
    grammar.alt(grammar.ref("Ann"), unwrap, fn(t, p) { format_term(t, p, []) }),
    grammar.alt(grammar.ref("App"), unwrap, fn(t, p) { format_term(t, p, []) }),
    grammar.alt(grammar.ref("Dot"), unwrap, fn(t, p) { format_term(t, p, []) }),
    grammar.alt(grammar.ref("Atom"), unwrap, fn(t, p) { format_term(t, p, []) }),
  ])
  // Lambda: x -> body
  |> grammar.rule("Lambda", [
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Arrow"),
        grammar.ref("Expr"),
      ]),
      make_lambda,
      fn(t, p) { format_term(t, p, []) },
    ),
  ])
  // Pi type: (x : A) -> B
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
      fn(t, p) { format_term(t, p, []) },
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
      fn(t, p) { format_term(t, p, []) },
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
      fn(t, p) { format_term(t, p, []) },
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
      fn(t, p) { format_term(t, p, []) },
    ),
  ])
  // Atoms - the building blocks
  |> grammar.rule("Atom", [
    // Constructor with args: #Name(arg)
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Hash"),
        grammar.token_pattern("Ident"),
        grammar.token_pattern("LParen"),
        grammar.ref("Expr"),
        grammar.token_pattern("RParen"),
      ]),
      make_constructor_app,
      fn(t, p) { format_term(t, p, []) },
    ),
    // Constructor without args: #Name
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Hash"),
        grammar.token_pattern("Ident"),
      ]),
      make_constructor,
      fn(t, p) { format_term(t, p, []) },
    ),
    // Type universe with level: $Type(1)
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Dollar"),
        grammar.token_pattern("Ident"),
        grammar.token_pattern("LParen"),
        grammar.token_pattern("Number"),
        grammar.token_pattern("RParen"),
      ]),
      make_typ_with_level,
      fn(t, p) { format_term(t, p, []) },
    ),
    // Type universe without level: $Type
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Dollar"),
        grammar.token_pattern("Ident"),
      ]),
      make_typ_or_litt,
      fn(t, p) { format_term(t, p, []) },
    ),
    // Hole with id: ?1
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Question"),
        grammar.token_pattern("Number"),
      ]),
      make_hole_with_id,
      fn(t, p) { format_term(t, p, []) },
    ),
    // Hole without id: ?
    grammar.alt(grammar.token_pattern("Question"), make_hole, fn(t, p) { format_term(t, p, []) }),
    // Empty record: {}
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LBrace"),
        grammar.token_pattern("RBrace"),
      ]),
      make_empty_record,
      fn(t, p) { format_term(t, p, []) },
    ),
    // Variable
    grammar.alt(grammar.token_pattern("Ident"), make_var, fn(t, p) { format_term(t, p, []) }),
    // Number literal
    grammar.alt(grammar.token_pattern("Number"), make_literal, fn(t, p) { format_term(t, p, []) }),
    // Parenthesized expression
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LParen"),
        grammar.ref("Expr"),
        grammar.token_pattern("RParen"),
      ]),
      unwrap_parens,
      fn(t, p) { format_term(t, p, []) },
    ),
  ])
  // Field list: x: expr, y: expr (internal rule - returns List, not Term)
  // Note: This is a workaround - the grammar DSL expects all rules to return Term
  // For now, we handle records directly in the Atom rule
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
    [TokenValue(name_token), _, AstValue(body)] ->
      Term(Lam(name_token.value, body), grammar.span_from_token(name_token, "input"))
    _ -> panic as "Expected lambda (x -> body)"
  }
}

fn make_pi(values) {
  case values {
    [_, TokenValue(name_token), _, AstValue(in_term), _, _, AstValue(out_term)] ->
      Term(Pi(name_token.value, in_term, out_term), in_term.span)
    _ -> panic as "Expected Pi type ((x : A) -> B)"
  }
}

fn make_annotation(values) {
  case values {
    [AstValue(term), _, AstValue(typ)] ->
      Term(Ann(term, typ), term.span)
    _ -> panic as "Expected annotation (term : type)"
  }
}

fn make_application(values) {
  case values {
    [AstValue(fun), _, AstValue(arg), _] ->
      Term(App(fun, arg), grammar.span_from_token(values |> get_first_token, "input"))
    _ -> panic as "Expected f(args)"
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

fn make_var(values) {
  case values {
    [TokenValue(token)] -> Term(Var(0), grammar.span_from_token(token, "input"))
    _ -> panic as "Expected identifier"
  }
}

fn make_var_or_typ(values) {
  case values {
    [TokenValue(token)] -> {
      // Check if it's a type universe ($Type, $Type1, etc.)
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

fn make_hole_with_id(values) {
  case values {
    [_, TokenValue(id_token)] -> {
      case int.parse(id_token.value) {
        Ok(id) -> Term(Hole(id), grammar.span_from_token(id_token, "input"))
        Error(_) -> Term(Hole(0), grammar.span_from_token(id_token, "input"))
      }
    }
    _ -> panic as "Expected hole with id (?1)"
  }
}

fn make_typ_or_litt(values) {
  case values {
    [_, TokenValue(token)] -> {
      // Check what follows $ prefix
      case token.value {
        "Type" -> Term(Typ(0), grammar.span_from_token(token, "input"))
        "I32" -> Term(LitT(I32T), grammar.span_from_token(token, "input"))
        "I64" -> Term(LitT(I64T), grammar.span_from_token(token, "input"))
        "F32" -> Term(LitT(F32T), grammar.span_from_token(token, "input"))
        "F64" -> Term(LitT(F64T), grammar.span_from_token(token, "input"))
        "U32" -> Term(LitT(U32T), grammar.span_from_token(token, "input"))
        "U64" -> Term(LitT(U64T), grammar.span_from_token(token, "input"))
        // Otherwise it's a constructor-like type
        _ -> Term(Ctr(token.value, Term(Hole(0), grammar.span_from_token(token, "input"))), grammar.span_from_token(token, "input"))
      }
    }
    _ -> panic as "Expected $Type or $I32"
  }
}

fn make_typ_with_level(values) {
  case values {
    [_, TokenValue(type_token), _, TokenValue(level_token), _] -> {
      case type_token.value {
        "Type" -> {
          case int.parse(level_token.value) {
            Ok(level) -> Term(Typ(level), grammar.span_from_token(type_token, "input"))
            Error(_) -> Term(Typ(0), grammar.span_from_token(type_token, "input"))
          }
        }
        _ -> panic as "Expected $Type(n)"
      }
    }
    _ -> panic as "Expected $Type(n)"
  }
}

fn make_constructor(values) {
  case values {
    [_, TokenValue(token)] ->
      Term(Ctr(token.value, Term(Hole(0), grammar.span_from_token(token, "input"))), grammar.span_from_token(token, "input"))
    _ -> panic as "Expected constructor (#Name)"
  }
}

fn make_constructor_app(values) {
  case values {
    [_, TokenValue(name_token), _, AstValue(arg), _] ->
      Term(Ctr(name_token.value, arg), grammar.span_from_token(name_token, "input"))
    _ -> panic as "Expected constructor application (#Name(arg))"
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

fn format_term(term: Term, parent_prec: Int, bindings: List(String)) -> formatter.Doc {
  case term.data {
    Var(index) -> {
      case get_binding(bindings, index) {
        Ok(name) -> formatter.text(name)
        Error(_) -> formatter.concat([formatter.text("var"), formatter.text(int.to_string(index))])
      }
    }
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
    Typ(level) -> {
      case level {
        0 -> formatter.text("$Type")
        _ -> formatter.concat([formatter.text("$Type("), formatter.text(int.to_string(level)), formatter.text(")")])
      }
    }
    Hole(id) -> {
      case id {
        0 -> formatter.text("?")
        _ -> formatter.concat([formatter.text("?"), formatter.text(int.to_string(id))])
      }
    }
    LitT(typ) -> {
      case typ {
        I32T -> formatter.text("$I32")
        I64T -> formatter.text("$I64")
        U32T -> formatter.text("$U32")
        U64T -> formatter.text("$U64")
        F32T -> formatter.text("$F32")
        F64T -> formatter.text("$F64")
      }
    }
    Ctr(tag, arg) -> {
      // Check if arg is a Hole - if so, just show the tag
      case arg.data {
        Hole(_) -> formatter.concat([formatter.text("#"), formatter.text(tag)])
        _ -> formatter.concat([formatter.text("#"), formatter.text(tag), formatter.text("("), format_term(arg, 50, bindings), formatter.text(")")])
      }
    }
    Dot(arg, field) -> {
      let inner =
        formatter.concat([
          format_term(arg, 90, bindings),
          formatter.text("."),
          formatter.text(field),
        ])
      wrap_parens(inner, 90 < parent_prec)
    }
    Ann(term, typ) -> {
      let inner =
        formatter.concat([
          format_term(term, 50, bindings),
          formatter.text(" : "),
          format_term(typ, 50, bindings),
        ])
      wrap_parens(inner, 50 < parent_prec)
    }
    Pi(name, in_term, out_term) -> {
      let inner =
        formatter.concat([
          formatter.text("("),
          formatter.text(name),
          formatter.text(" : "),
          format_term(in_term, 50, bindings),
          formatter.text(") -> "),
          format_term(out_term, 65, [name, ..bindings]),
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
                formatter.text(": "),
                format_term(value, 50, bindings),
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
          formatter.text(name),
          formatter.text(" -> "),
          format_term(body, 70, [name, ..bindings]),
        ])
      wrap_parens(inner, 70 < parent_prec)
    }
    App(fun, arg) -> {
      let inner =
        formatter.concat([
          format_term(fun, 85, bindings),
          formatter.text("("),
          format_term(arg, 85, bindings),
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

fn get_binding(bindings: List(String), index: Int) -> Result(String, Nil) {
  case bindings, index {
    [], _ -> Error(Nil)
    [x, ..], 0 -> Ok(x)
    [_, ..xs], _ -> get_binding(xs, index - 1)
  }
}
