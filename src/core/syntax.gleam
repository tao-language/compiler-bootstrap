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
  type Literal, type LiteralType, type Term, Ann, App, Ctr, Dot, F32, F32T, F64, F64T, Hole, I32, I32T, I64, I64T, Lam, Lit,
  LitT, Pi, Rcd, Term, Typ, U32, U32T, U64, U64T, Var,
}
import gleam/float
import gleam/int
import gleam/list
import gleam/result
import gleam/string
import syntax/formatter
import syntax/grammar.{ParseError, type ParseError, type Span, AstValue, TokenValue}
import syntax/lexer.{type Token}

// ============================================================================
// NAMED TERM TYPE (Intermediate AST)
// ============================================================================
/// Intermediate AST with named variables (before De Bruijn conversion).
/// This allows proper variable shadowing resolution.
pub type NamedTerm {
  NVar(name: String, span: Span)
  NLit(value: Literal, span: Span)
  NLam(name: String, body: NamedTerm, span: Span)
  NPi(name: String, in_type: NamedTerm, out_type: NamedTerm, span: Span)
  NApp(fun: NamedTerm, arg: NamedTerm, span: Span)
  NAnn(term: NamedTerm, typ: NamedTerm, span: Span)
  NDot(arg: NamedTerm, field: String, span: Span)
  NCtr(tag: String, arg: NamedTerm, span: Span)
  NTyp(level: Int, span: Span)
  NHole(id: Int, span: Span)
  NLitT(typ: LiteralType, span: Span)
  NRcd(fields: List(#(String, NamedTerm)), span: Span)
}

// ============================================================================
// PARSE VALUE TYPE
// ============================================================================
/// Wrapper type to allow grammar rules to return different types.
/// Some rules return NamedTerm, others return List(#(String, NamedTerm)) for field lists.
pub type ParseValue {
  AsTerm(NamedTerm)
  AsFields(List(#(String, NamedTerm)))
}

// ============================================================================
// PUBLIC API
// ============================================================================

/// Convert named variables to De Bruijn indices.
/// Tracks bound variable names in an environment.
fn named_to_de_bruijn_loop(term: NamedTerm, env: List(String)) -> Term {
  case term {
    NVar(name, span) -> {
      // Find the variable in the environment (0 = innermost)
      case find_in_env(env, name, 0) {
        Ok(index) -> Term(Var(index), span)
        Error(_) -> Term(Var(0), span) // Free variable
      }
    }
    NLit(value, span) -> Term(Lit(value), span)
    NLam(name, body, span) -> {
      let body_db = named_to_de_bruijn_loop(body, [name, ..env])
      Term(Lam(name, body_db), span)
    }
    NPi(name, in_type, out_type, span) -> {
      let in_db = named_to_de_bruijn_loop(in_type, env)
      let out_db = named_to_de_bruijn_loop(out_type, [name, ..env])
      Term(Pi(name, in_db, out_db), span)
    }
    NApp(fun, arg, span) -> {
      let fun_db = named_to_de_bruijn_loop(fun, env)
      let arg_db = named_to_de_bruijn_loop(arg, env)
      Term(App(fun_db, arg_db), span)
    }
    NAnn(term, typ, span) -> {
      let term_db = named_to_de_bruijn_loop(term, env)
      let typ_db = named_to_de_bruijn_loop(typ, env)
      Term(Ann(term_db, typ_db), span)
    }
    NDot(arg, field, span) -> {
      let arg_db = named_to_de_bruijn_loop(arg, env)
      Term(Dot(arg_db, field), span)
    }
    NCtr(tag, arg, span) -> {
      let arg_db = named_to_de_bruijn_loop(arg, env)
      Term(Ctr(tag, arg_db), span)
    }
    NTyp(level, span) -> Term(Typ(level), span)
    NHole(id, span) -> Term(Hole(id), span)
    NLitT(typ, span) -> Term(LitT(typ), span)
    NRcd(fields, span) -> {
      let fields_db = fields |> list.map(fn(f) {
        let #(name, value) = f
        #(name, named_to_de_bruijn_loop(value, env))
      })
      Term(Rcd(fields_db), span)
    }
  }
}

fn find_in_env(env: List(String), name: String, index: Int) -> Result(Int, Nil) {
  case env {
    [] -> Error(Nil)
    [n, ..] if n == name -> Ok(index)
    [_, ..rest] -> find_in_env(rest, name, index + 1)
  }
}

/// Convert NamedTerm to Term with proper De Bruijn indices.
pub fn named_to_de_bruijn(term: NamedTerm) -> Term {
  named_to_de_bruijn_loop(term, [])
}

fn parse_value_to_term(value: ParseValue) -> Result(Term, ParseError) {
  case value {
    AsTerm(named_term) -> Ok(named_to_de_bruijn(named_term))
    AsFields(_) -> Error(ParseError(0, "expression", "field list"))
  }
}

pub fn parse(source: String) -> grammar.ParseResult(Term) {
  let parsed: grammar.ParseResult(ParseValue) = grammar.parse(core_grammar(), source)
  case parsed {
    grammar.ParseResult(ast, errors) -> {
      case ast {
        AsTerm(named_term) -> {
          let term = named_to_de_bruijn(named_term)
          grammar.ParseResult(term, errors)
        }
        AsFields(_) -> {
          let err = ParseError(0, "expression", "field list")
          grammar.ParseResult(ast: panic as "Parse failed", errors: [err, ..errors])
        }
      }
    }
  }
}

pub fn format(term: Term) -> String {
  format_term(term, -1, []) |> formatter.render_default
}

// ============================================================================
// GRAMMAR DEFINITION
// ============================================================================

pub fn core_grammar() -> grammar.Grammar(ParseValue) {
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
    grammar.alt(grammar.ref("Lambda"), unwrap, fn(_, p) { formatter.text("") }),
    grammar.alt(grammar.ref("Pi"), unwrap, fn(_, p) { formatter.text("") }),
    grammar.alt(grammar.ref("Ann"), unwrap, fn(_, p) { formatter.text("") }),
    grammar.alt(grammar.ref("App"), unwrap, fn(_, p) { formatter.text("") }),
    grammar.alt(grammar.ref("Dot"), unwrap, fn(_, p) { formatter.text("") }),
    grammar.alt(grammar.ref("Atom"), unwrap, fn(_, p) { formatter.text("") }),
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
      fn(v, p) { format_value(v, p) },
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
      fn(v, p) { format_value(v, p) },
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
      fn(v, p) { format_value(v, p) },
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
      fn(v, p) { format_value(v, p) },
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
      fn(v, p) { format_value(v, p) },
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
      fn(v, p) { format_value(v, p) },
    ),
    // Constructor without args: #Name
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Hash"),
        grammar.token_pattern("Ident"),
      ]),
      make_constructor,
      fn(v, p) { format_value(v, p) },
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
      fn(v, p) { format_value(v, p) },
    ),
    // Type universe without level: $Type
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Dollar"),
        grammar.token_pattern("Ident"),
      ]),
      make_typ_or_litt,
      fn(v, p) { format_value(v, p) },
    ),
    // Hole with id: ?1
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Question"),
        grammar.token_pattern("Number"),
      ]),
      make_hole_with_id,
      fn(v, p) { format_value(v, p) },
    ),
    // Hole without id: ?
    grammar.alt(grammar.token_pattern("Question"), make_hole, fn(v, p) { format_value(v, p) }),
    // Empty record: {}
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LBrace"),
        grammar.token_pattern("RBrace"),
      ]),
      make_empty_record,
      fn(v, p) { format_value(v, p) },
    ),
    // Variable
    grammar.alt(grammar.token_pattern("Ident"), make_var, fn(v, p) { format_value(v, p) }),
    // Number literal
    grammar.alt(grammar.token_pattern("Number"), make_literal, fn(v, p) { format_value(v, p) }),
    // Parenthesized expression
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LParen"),
        grammar.ref("Expr"),
        grammar.token_pattern("RParen"),
      ]),
      unwrap_parens,
      fn(v, p) { format_value(v, p) },
    ),
    // Record with fields: {x: 1, y: 2}
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LBrace"),
        grammar.ref("FieldList"),
        grammar.token_pattern("RBrace"),
      ]),
      make_record_with_fields,
      fn(v, p) { format_value(v, p) },
    ),
  ])
  // Field list: x: expr, y: expr (returns AsFields)
  |> grammar.rule("FieldList", [
    // Multiple fields: x: expr, rest... (try this first for longest match)
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Colon"),
        grammar.ref("Expr"),
        grammar.token_pattern("Comma"),
        grammar.ref("FieldList"),
      ]),
      make_field_cons,
      fn(_, _) { formatter.text("") },
    ),
    // Single field: x: expr
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Colon"),
        grammar.ref("Expr"),
      ]),
      make_single_field,
      fn(_, _) { formatter.text("") },
    ),
  ])
}

// ============================================================================
// CONSTRUCTOR HELPERS
// ============================================================================

fn unwrap(values) -> ParseValue {
  case values {
    [AstValue(AsTerm(term))] -> AsTerm(term)
    _ -> panic as "Expected single NamedTerm value"
  }
}

fn unwrap_parens(values) -> ParseValue {
  case values {
    [_, AstValue(AsTerm(term)), _] -> AsTerm(term)
    _ -> panic as "Expected (expr)"
  }
}

fn make_lambda(values) -> ParseValue {
  case values {
    [TokenValue(name_token), _, AstValue(AsTerm(body))] ->
      AsTerm(NLam(name_token.value, body, grammar.span_from_token(name_token, "input")))
    _ -> panic as "Expected lambda (x -> body)"
  }
}

fn make_pi(values) -> ParseValue {
  case values {
    [_, TokenValue(name_token), _, AstValue(AsTerm(in_term)), _, _, AstValue(AsTerm(out_term))] ->
      AsTerm(NPi(name_token.value, in_term, out_term, get_span(in_term)))
    _ -> panic as "Expected Pi type ((x : A) -> B)"
  }
}

fn make_annotation(values) -> ParseValue {
  case values {
    [AstValue(AsTerm(term)), _, AstValue(AsTerm(typ))] ->
      AsTerm(NAnn(term, typ, get_span(term)))
    _ -> panic as "Expected annotation (term : type)"
  }
}

fn make_application(values) -> ParseValue {
  case values {
    [AstValue(AsTerm(fun)), _, AstValue(AsTerm(arg)), _] ->
      AsTerm(NApp(fun, arg, grammar.span_from_token(values |> get_first_token, "input")))
    _ -> panic as "Expected f(args)"
  }
}

fn make_field_access(values) -> ParseValue {
  case values {
    [AstValue(AsTerm(arg)), _, TokenValue(field_token)] ->
      AsTerm(NDot(arg, field_token.value, get_span(arg)))
    _ -> panic as "Expected field access (expr.field)"
  }
}

fn make_empty_record(values) -> ParseValue {
  case values {
    [_, _] -> AsTerm(NRcd([], grammar.span_from_token(values |> get_first_token, "input")))
    _ -> panic as "Expected empty record {}"
  }
}

fn make_var(values) -> ParseValue {
  case values {
    [TokenValue(token)] -> AsTerm(NVar(token.value, grammar.span_from_token(token, "input")))
    _ -> panic as "Expected identifier"
  }
}

fn make_literal(values) -> ParseValue {
  case values {
    [TokenValue(token)] -> {
      case int.parse(token.value) {
        Ok(n) -> AsTerm(NLit(I32(n), grammar.span_from_token(token, "input")))
        Error(_) -> AsTerm(NLit(I32(0), grammar.span_from_token(token, "input")))
      }
    }
    _ -> panic as "Expected number token"
  }
}

fn make_hole(values) -> ParseValue {
  case values {
    [TokenValue(token)] -> {
      case token.value {
        "?" -> AsTerm(NHole(0, grammar.span_from_token(token, "input")))
        _ -> panic as "Expected ? operator"
      }
    }
    _ -> panic as "Expected hole (?)"
  }
}

fn make_hole_with_id(values) -> ParseValue {
  case values {
    [_, TokenValue(id_token)] -> {
      case int.parse(id_token.value) {
        Ok(id) -> AsTerm(NHole(id, grammar.span_from_token(id_token, "input")))
        Error(_) -> AsTerm(NHole(0, grammar.span_from_token(id_token, "input")))
      }
    }
    _ -> panic as "Expected hole with id (?1)"
  }
}

fn make_typ_or_litt(values) -> ParseValue {
  case values {
    [_, TokenValue(token)] -> {
      // Check what follows $ prefix
      case token.value {
        "Type" -> AsTerm(NTyp(0, grammar.span_from_token(token, "input")))
        "I32" -> AsTerm(NLitT(I32T, grammar.span_from_token(token, "input")))
        "I64" -> AsTerm(NLitT(I64T, grammar.span_from_token(token, "input")))
        "F32" -> AsTerm(NLitT(F32T, grammar.span_from_token(token, "input")))
        "F64" -> AsTerm(NLitT(F64T, grammar.span_from_token(token, "input")))
        "U32" -> AsTerm(NLitT(U32T, grammar.span_from_token(token, "input")))
        "U64" -> AsTerm(NLitT(U64T, grammar.span_from_token(token, "input")))
        // Otherwise it's a constructor-like type
        _ -> AsTerm(NCtr(token.value, NHole(0, grammar.span_from_token(token, "input")), grammar.span_from_token(token, "input")))
      }
    }
    _ -> panic as "Expected $Type or $I32"
  }
}

fn make_typ_with_level(values) -> ParseValue {
  case values {
    [_, TokenValue(type_token), _, TokenValue(level_token), _] -> {
      case type_token.value {
        "Type" -> {
          case int.parse(level_token.value) {
            Ok(level) -> AsTerm(NTyp(level, grammar.span_from_token(type_token, "input")))
            Error(_) -> AsTerm(NTyp(0, grammar.span_from_token(type_token, "input")))
          }
        }
        _ -> panic as "Expected $Type(n)"
      }
    }
    _ -> panic as "Expected $Type(n)"
  }
}

fn make_constructor(values) -> ParseValue {
  case values {
    [_, TokenValue(token)] ->
      AsTerm(NCtr(token.value, NHole(0, grammar.span_from_token(token, "input")), grammar.span_from_token(token, "input")))
    _ -> panic as "Expected constructor (#Name)"
  }
}

fn make_constructor_app(values) -> ParseValue {
  case values {
    [_, TokenValue(name_token), _, AstValue(AsTerm(arg)), _] ->
      AsTerm(NCtr(name_token.value, arg, grammar.span_from_token(name_token, "input")))
    _ -> panic as "Expected constructor application (#Name(arg))"
  }
}

fn make_record_with_fields(values) -> ParseValue {
  case values {
    [_, AstValue(AsFields(fields)), _] ->
      AsTerm(NRcd(fields, grammar.span_from_token(values |> get_first_token, "input")))
    _ -> panic as "Expected record with fields {x: 1, ...}"
  }
}

fn make_single_field(values) -> ParseValue {
  case values {
    [TokenValue(name_token), _, AstValue(AsTerm(value))] ->
      AsFields([#(name_token.value, value)])
    _ -> panic as "Expected single field (name: value)"
  }
}

fn make_field_cons(values) -> ParseValue {
  case values {
    [TokenValue(name_token), _, AstValue(AsTerm(value)), _, AstValue(AsFields(rest))] ->
      AsFields([#(name_token.value, value), ..rest])
    _ -> panic as "Expected field list (name: value, ...)"
  }
}

fn get_first_token(values: List(grammar.Value(ParseValue))) -> Token {
  case values {
    [TokenValue(token), ..] -> token
    [AstValue(AsTerm(term)), ..] -> {
      get_span(term) |> span_to_token
    }
    _ -> panic as "Expected at least one value"
  }
}

fn span_to_token(span: Span) -> Token {
  lexer.Token("Unknown", "", span.start_line, span.end_col, span.start_line, span.start_col)
}

/// Get the span from a NamedTerm.
fn get_span(term: NamedTerm) -> Span {
  case term {
    NVar(_, span) -> span
    NLit(_, span) -> span
    NLam(_, _, span) -> span
    NPi(_, _, _, span) -> span
    NApp(_, _, span) -> span
    NAnn(_, _, span) -> span
    NDot(_, _, span) -> span
    NCtr(_, _, span) -> span
    NTyp(_, span) -> span
    NHole(_, span) -> span
    NLitT(_, span) -> span
    NRcd(_, span) -> span
  }
}

// ============================================================================
// FORMATTER
// ============================================================================

fn format_value(value: ParseValue, parent_prec: Int) -> formatter.Doc {
  case value {
    AsTerm(named_term) -> {
      let term = named_to_de_bruijn(named_term)
      format_term(term, parent_prec, [])
    }
    AsFields(_) -> formatter.text("<fields>")
  }
}

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
