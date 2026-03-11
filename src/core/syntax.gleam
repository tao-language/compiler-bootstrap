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
  type Case, type Literal, type LiteralType, type Pattern, type Term, Ann, App, Call, Case,
  Comptime, Ctr, Dot, Err, F32, F32T, F64, F64T, Hole, I32, I32T, I64, I64T, Lam, Lit, LitT, Match,
  PAny, PAs, PCtr, PLit, PLitT, PRcd, PTyp, Pi, Rcd, Term, Typ, U32, U32T, U64, U64T, Var,
}
import gleam/float
import gleam/int
import gleam/list
import syntax/formatter
import syntax/grammar.{type Span, AstValue, ParseResult, TokenValue}
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
  /// Pattern matching: match arg with motive returning cases
  NMatch(arg: NamedTerm, motive: NamedTerm, cases: List(NamedCase), span: Span)
  /// Built-in call: call name(args)
  NCall(name: String, args: List(NamedTerm), span: Span)
  /// Compile-time evaluation: comptime { term }
  NComptime(term: NamedTerm, span: Span)
  /// Error placeholder for parse failures
  NErr(message: String, span: Span)
}

/// Pattern in match expressions
pub type NamedPattern {
  NPAny(span: Span)
  NPAs(pattern: NamedPattern, name: String, span: Span)
  NPTyp(level: Int, span: Span)
  NPLit(value: Literal, span: Span)
  NPLitT(typ: LiteralType, span: Span)
  NPRcd(fields: List(#(String, NamedPattern)), span: Span)
  NPCtr(tag: String, arg: NamedPattern, span: Span)
}

/// Case in match expression
pub type NamedCase {
  NCase(pattern: NamedPattern, body: NamedTerm, span: Span)
}

// ============================================================================
// PARSE VALUE TYPE
// ============================================================================
/// Wrapper type to allow grammar rules to return different types.
/// Some rules return NamedTerm, others return List(#(String, NamedTerm)) for field lists.
pub type ParseValue {
  AsTerm(NamedTerm)
  AsFields(List(#(String, NamedTerm)))
  AsCases(List(NamedCase))
  AsPattern(NamedPattern)
  AsArgs(List(NamedTerm))
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
    NMatch(arg, motive, cases, span) -> {
      let arg_db = named_to_de_bruijn_loop(arg, env)
      let motive_db = named_to_de_bruijn_loop(motive, env)
      let cases_db = cases |> list.map(fn(c) { named_case_to_de_bruijn(c, env) })
      Term(Match(arg_db, motive_db, cases_db), span)
    }
    NCall(name, args, span) -> {
      let args_db = args |> list.map(fn(a) { named_to_de_bruijn_loop(a, env) })
      Term(Call(name, args_db), span)
    }
    NComptime(term, span) -> {
      let term_db = named_to_de_bruijn_loop(term, env)
      Term(Comptime(term_db), span)
    }
    NErr(message, span) -> {
      Term(core.Err(message), span)
    }
  }
}

/// Convert NamedCase to Case with De Bruijn indices.
fn named_case_to_de_bruijn(named_case: NamedCase, env: List(String)) -> Case {
  let NCase(pattern, body, span) = named_case
  let pattern_db = named_pattern_to_de_bruijn(pattern)
  let body_db = named_to_de_bruijn_loop(body, env)
  Case(pattern_db, body_db, span)
}

/// Convert NamedPattern to Pattern with De Bruijn indices.
/// Note: Patterns don't bind variables, so no environment needed.
fn named_pattern_to_de_bruijn(pattern: NamedPattern) -> Pattern {
  case pattern {
    NPAny(_span) -> PAny
    NPAs(inner, name, _span) -> {
      let inner_db = named_pattern_to_de_bruijn(inner)
      PAs(inner_db, name)
    }
    NPTyp(level, _span) -> PTyp(level)
    NPLit(value, _span) -> PLit(value)
    NPLitT(typ, _span) -> PLitT(typ)
    NPRcd(fields, _span) -> {
      let fields_db = fields |> list.map(fn(f) {
        let #(name, pat) = f
        #(name, named_pattern_to_de_bruijn(pat))
      })
      PRcd(fields_db)
    }
    NPCtr(tag, arg, _span) -> {
      let arg_db = named_pattern_to_de_bruijn(arg)
      PCtr(tag, arg_db)
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

pub fn parse(source: String) -> grammar.ParseResult(Term) {
  // Create an error placeholder AST to use if parsing fails
  let error_ast = AsTerm(NErr("Parse error", grammar.Span("", 0, 0, 0, 0)))
  let parsed: grammar.ParseResult(ParseValue) = grammar.parse(core_grammar(), source, error_ast)
  case parsed {
    ParseResult(ast: ast, errors: errors) -> {
      case ast {
        AsTerm(NErr(msg, _)) -> {
          // Got error AST from grammar.parse - include the message
          let placeholder = Term(core.Err("Parse error: " <> msg), grammar.Span("", 0, 0, 0, 0))
          grammar.ParseResult(ast: placeholder, errors: errors)
        }
        AsTerm(named_term) -> {
          // Got normal AST - check for errors
          case errors {
            [_, ..] -> {
              // Has errors - return error AST with error list
              let placeholder = Term(core.Err("Parse error: see errors list"), grammar.Span("", 0, 0, 0, 0))
              grammar.ParseResult(ast: placeholder, errors: errors)
            }
            [] -> {
              // No errors - process the AST
              let term = named_to_de_bruijn(named_term)
              grammar.ParseResult(ast: term, errors: [])
            }
          }
        }
        AsFields(_) -> {
          let placeholder = Term(core.Err("Expected expression, got field list"), grammar.Span("", 0, 0, 0, 0))
          grammar.ParseResult(ast: placeholder, errors: [grammar.ParseError(0, "expression", "field list")])
        }
        AsCases(_) -> {
          let placeholder = Term(core.Err("Expected expression, got case list"), grammar.Span("", 0, 0, 0, 0))
          grammar.ParseResult(ast: placeholder, errors: [grammar.ParseError(0, "expression", "case list")])
        }
        AsPattern(_) -> {
          let placeholder = Term(core.Err("Expected expression, got pattern"), grammar.Span("", 0, 0, 0, 0))
          grammar.ParseResult(ast: placeholder, errors: [grammar.ParseError(0, "expression", "pattern")])
        }
        AsArgs(_) -> {
          let placeholder = Term(core.Err("Expected expression, got argument list"), grammar.Span("", 0, 0, 0, 0))
          grammar.ParseResult(ast: placeholder, errors: [grammar.ParseError(0, "expression", "argument list")])
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
  |> grammar.token("Equal")
  |> grammar.token("Comma")
  |> grammar.token("Arrow")
  |> grammar.token("Dollar")
  |> grammar.token("Hash")
  |> grammar.token("Question")
  |> grammar.token("Underscore")
  |> grammar.token("At")
  |> grammar.token("Percent")
  |> grammar.token("PercentMatch")
  |> grammar.token("PercentCall")
  |> grammar.token("PercentComptime")
  |> grammar.token("Tilde")
  |> grammar.token("Pipe")
  |> grammar.token("Let")
  |> grammar.token("In")
  // Main expression rule (lowest precedence first)
  |> grammar.rule("Expr", [
    // Keywords first (Match, Call, Comptime, Let) - these start with special tokens
    grammar.alt(grammar.ref("Match"), unwrap, fn(_, _p) { formatter.text("") }),
    grammar.alt(grammar.ref("Call"), unwrap, fn(_, _p) { formatter.text("") }),
    grammar.alt(grammar.ref("Comptime"), unwrap, fn(_, _p) { formatter.text("") }),
    grammar.alt(grammar.ref("Let"), unwrap, fn(_, _p) { formatter.text("") }),
    // Then other expressions
    grammar.alt(grammar.ref("Lambda"), unwrap, fn(_, _p) { formatter.text("") }),
    grammar.alt(grammar.ref("Pi"), unwrap, fn(_, _p) { formatter.text("") }),
    grammar.alt(grammar.ref("Ann"), unwrap, fn(_, _p) { formatter.text("") }),
    grammar.alt(grammar.ref("App"), unwrap, fn(_, _p) { formatter.text("") }),
    grammar.alt(grammar.ref("Dot"), unwrap, fn(_, _p) { formatter.text("") }),
    grammar.alt(grammar.ref("Atom"), unwrap, fn(_, _p) { formatter.text("") }),
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
  // Match: %match arg ~ motive { | pat -> body ... }
  |> grammar.rule("Match", [
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("PercentMatch"),
        grammar.ref("Expr"),
        grammar.token_pattern("Tilde"),
        grammar.ref("Expr"),
        grammar.token_pattern("LBrace"),
        grammar.ref("Cases"),
        grammar.token_pattern("RBrace"),
      ]),
      make_match,
      fn(v, p) { format_value(v, p) },
    ),
  ])
  // Call: %call name(args)
  |> grammar.rule("Call", [
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("PercentCall"),
        grammar.token_pattern("Ident"),  // Simple function name for now
        grammar.token_pattern("LParen"),
        grammar.ref("ArgList"),
        grammar.token_pattern("RParen"),
      ]),
      make_call,
      fn(v, p) { format_value(v, p) },
    ),
  ])
  // Comptime: %comptime term
  |> grammar.rule("Comptime", [
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("PercentComptime"),
        grammar.ref("Expr"),
      ]),
      make_comptime,
      fn(v, p) { format_value(v, p) },
    ),
  ])
  // Let: let name = value in body
  |> grammar.rule("Let", [
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Let"),
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Equal"),
        grammar.ref("Expr"),
        grammar.token_pattern("In"),
        grammar.ref("Expr"),
      ]),
      make_let,
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
  // Cases: single | pattern -> body (multiple cases not yet supported)
  |> grammar.rule("Cases", [
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Pipe"),
        grammar.ref("Pattern"),
        grammar.token_pattern("Arrow"),
        grammar.ref("Expr"),
      ]),
      make_single_case_list,
      fn(_, _) { formatter.text("") },
    ),
  ])
  // Pattern: x, _, x @ pat, Type, 42, $I32, {fields}, #Name(pat)
  |> grammar.rule("Pattern", [
    // Variable pattern: x
    grammar.alt(
      grammar.token_pattern("Ident"),
      make_pattern_var,
      fn(_, _) { formatter.text("") },
    ),
    // Wildcard: _
    grammar.alt(grammar.token_pattern("Underscore"), make_pattern_any, fn(_, _) { formatter.text("") }),
    // As-pattern: x @ pat
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Ident"),
        grammar.token_pattern("At"),
        grammar.ref("Pattern"),
      ]),
      make_pattern_as,
      fn(_, _) { formatter.text("") },
    ),
    // Constructor pattern: #Name(pat)
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Hash"),
        grammar.token_pattern("Ident"),
        grammar.token_pattern("LParen"),
        grammar.ref("Pattern"),
        grammar.token_pattern("RParen"),
      ]),
      make_pattern_ctr,
      fn(_, _) { formatter.text("") },
    ),
    // Literal pattern: 42
    grammar.alt(grammar.token_pattern("Number"), make_pattern_lit, fn(_, _) { formatter.text("") }),
  ])
  // Argument list: expr, expr, ...
  |> grammar.rule("ArgList", [
    // Single arg
    grammar.alt(
      grammar.seq([grammar.ref("Expr")]),
      make_single_arg,
      fn(_, _) { formatter.text("") },
    ),
    // Multiple args: expr, args...
    grammar.alt(
      grammar.seq([
        grammar.ref("Expr"),
        grammar.token_pattern("Comma"),
        grammar.ref("ArgList"),
      ]),
      make_arg_cons,
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

// Match, Call, Comptime constructors
fn make_match(values) -> ParseValue {
  case values {
    [_, AstValue(AsTerm(arg)), _, AstValue(AsTerm(motive)), _, AstValue(AsCases(cases)), _] ->
      AsTerm(NMatch(arg, motive, cases, get_span(arg)))
    _ -> panic as "Expected match expression"
  }
}

fn make_call(values) -> ParseValue {
  case values {
    [_, AstValue(AsTerm(name_term)), _, AstValue(AsArgs(args)), _] -> {
      // Extract name from the term (could be NVar, NDot, etc.)
      let name = term_to_name(name_term)
      AsTerm(NCall(name, args, get_span(name_term)))
    }
    _ -> panic as "Expected call expression"
  }
}

fn term_to_name(term: NamedTerm) -> String {
  case term {
    NVar(name, _) -> name
    NDot(arg, field, _) -> term_to_name(arg) <> "." <> field
    _ -> "<unknown>"
  }
}

fn make_comptime(values) -> ParseValue {
  case values {
    [_, AstValue(AsTerm(term))] ->
      AsTerm(NComptime(term, grammar.span_from_token(values |> get_first_token, "input")))
    _ -> panic as "Expected comptime expression"
  }
}

fn make_let(values) -> ParseValue {
  case values {
    [_, TokenValue(name_token), _, AstValue(AsTerm(value)), _, AstValue(AsTerm(body))] -> {
      // Desugar: let name = value in body  →  (name -> body)(value)
      let name = name_token.value
      let span = grammar.span_from_token(name_token, "input")
      let lambda = NLam(name, body, span)
      let app = NApp(lambda, value, span)
      AsTerm(app)
    }
    _ -> panic as "Expected let binding"
  }
}

// Cases constructors
fn make_single_case_list(values) -> ParseValue {
  case values {
    [_, AstValue(AsPattern(pattern)), _, AstValue(AsTerm(body))] ->
      AsCases([NCase(pattern, body, get_span(body))])
    _ -> panic as "Expected single case"
  }
}

// Multiple cases support (future):
// fn make_cases_from_list(values) -> ParseValue { ... }
// fn parse_rest_cases(values: List(grammar.Value(ParseValue))) -> List(NamedCase) { ... }
// fn make_single_case(values) -> ParseValue { ... }
// fn make_case_cons(values) -> ParseValue { ... }

// Pattern constructors

/// Variable pattern: x (binds the matched value to x)
fn make_pattern_var(values) -> ParseValue {
  case values {
    [TokenValue(token)] -> {
      let span = grammar.span_from_token(token, "input")
      AsPattern(NPAs(NPAny(span), token.value, span))
    }
    _ -> panic as "Expected identifier pattern"
  }
}

fn make_pattern_any(values) -> ParseValue {
  case values {
    [TokenValue(token)] -> AsPattern(NPAny(grammar.span_from_token(token, "input")))
    _ -> panic as "Expected wildcard pattern"
  }
}

fn make_pattern_as(values) -> ParseValue {
  case values {
    [TokenValue(name_token), _, AstValue(AsPattern(pattern))] ->
      AsPattern(NPAs(pattern, name_token.value, grammar.span_from_token(name_token, "input")))
    _ -> panic as "Expected as-pattern"
  }
}

fn make_pattern_ctr(values) -> ParseValue {
  case values {
    [_, TokenValue(tag_token), _, _, AstValue(AsPattern(arg)), _] ->
      AsPattern(NPCtr(tag_token.value, arg, grammar.span_from_token(tag_token, "input")))
    _ -> panic as "Expected constructor pattern"
  }
}

fn make_pattern_lit(values) -> ParseValue {
  case values {
    [TokenValue(token)] -> {
      case int.parse(token.value) {
        Ok(n) -> AsPattern(NPLit(I32(n), grammar.span_from_token(token, "input")))
        Error(_) -> AsPattern(NPLit(I32(0), grammar.span_from_token(token, "input")))
      }
    }
    _ -> panic as "Expected literal pattern"
  }
}

// ArgList constructors
fn make_single_arg(values) -> ParseValue {
  case values {
    [AstValue(AsTerm(arg))] -> AsArgs([arg])
    _ -> panic as "Expected single argument"
  }
}

fn make_arg_cons(values) -> ParseValue {
  case values {
    [AstValue(AsTerm(arg)), _, AstValue(AsArgs(rest))] ->
      AsArgs([arg, ..rest])
    _ -> panic as "Expected argument list"
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
    NMatch(_, _, _, span) -> span
    NCall(_, _, span) -> span
    NComptime(_, span) -> span
    NErr(_, span) -> span
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
    AsCases(_) -> formatter.text("<cases>")
    AsPattern(_) -> formatter.text("<pattern>")
    AsArgs(_) -> formatter.text("<args>")
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
    Match(arg, motive, cases) -> {
      let case_docs = cases |> list.map(fn(c) {
        let Case(pattern, body, _) = c
        formatter.concat([
          formatter.text("  | "),
          format_pattern(pattern),
          formatter.text(" -> "),
          format_term(body, 70, bindings),
        ])
      })
      let inner = formatter.concat([
        formatter.text("%match "),
        format_term(arg, 85, bindings),
        formatter.text(" ~ "),
        format_term(motive, 85, bindings),
        formatter.text(" {\n"),
        list.intersperse(case_docs, formatter.text("\n")) |> formatter.concat,
        formatter.text("\n}"),
      ])
      wrap_parens(inner, 40 < parent_prec)
    }
    Call(name, args) -> {
      let arg_docs = args |> list.map(fn(a) { format_term(a, 85, bindings) })
      let inner = formatter.concat([
        formatter.text("%call "),
        formatter.text(name),
        formatter.text("("),
        list.intersperse(arg_docs, formatter.text(", ")) |> formatter.concat,
        formatter.text(")"),
      ])
      wrap_parens(inner, 85 < parent_prec)
    }
    Comptime(term) -> {
      let inner = formatter.concat([
        formatter.text("%comptime "),
        format_term(term, 50, bindings),
      ])
      wrap_parens(inner, 50 < parent_prec)
    }
    Err(message: msg) -> formatter.concat([formatter.text("<error: "), formatter.text(msg), formatter.text(">")])
  }
}

/// Format a pattern.
fn format_pattern(pattern: Pattern) -> formatter.Doc {
  case pattern {
    PAny -> formatter.text("_")
    PAs(inner, name) -> formatter.concat([
      formatter.text(name),
      formatter.text(" @ "),
      format_pattern(inner),
    ])
    PTyp(level) -> {
      case level {
        0 -> formatter.text("$Type")
        _ -> formatter.concat([formatter.text("$Type("), formatter.text(int.to_string(level)), formatter.text(")")])
      }
    }
    PLit(value) -> {
      case value {
        I32(n) -> formatter.text(int.to_string(n))
        _ -> formatter.text("<lit>")
      }
    }
    PLitT(typ) -> {
      case typ {
        I32T -> formatter.text("$I32")
        _ -> formatter.text("<litt>")
      }
    }
    PRcd(fields) -> {
      let field_docs = fields |> list.map(fn(f) {
        let #(name, pat) = f
        formatter.concat([
          formatter.text(name),
          formatter.text(": "),
          format_pattern(pat),
        ])
      })
      formatter.concat([
        formatter.text("{"),
        list.intersperse(field_docs, formatter.text(", ")) |> formatter.concat,
        formatter.text("}"),
      ])
    }
    PCtr(tag, arg) -> formatter.concat([
      formatter.text("#"),
      formatter.text(tag),
      formatter.text("("),
      format_pattern(arg),
      formatter.text(")"),
    ])
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
