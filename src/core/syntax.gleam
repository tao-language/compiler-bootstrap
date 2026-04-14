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
/// - Type annotations: `x : %I32`
/// - Field access: `record.field`
/// - Records: `{}`, `{x: 1}`, `{x: 1, y: 2}`
/// - Constructors: `#True`, `#Some`, `#Maybe(a)`
/// - Type universes: `%Type`, `%Type(1)`, `%Type(2)`
/// - Holes: `?`, `?1`, `?2` (unsolved metavariables)
/// - Literal types: `%I32`, `%I64`, `%F64`
///
/// Both parser and formatter are derived from this single grammar definition.
import core/ast.{
  type Case, type Literal, type LiteralType, type Pattern, type Term, Ann, App,
  Call, Case, Comptime, Ctr, Dot, Err, F32, F32T, F64, F64T, Fix, Hole, I32,
  I32T, I64, I64T, Lam, Lit, LitT, Match, PAny, PAs, PCtr, PUnit, PLit, PLitT, PRcd,
  PTyp, Pi, Rcd, Typ, U32, U32T, U64, U64T, Var, Unit,
  ILitT, FLitT, IntLit, FloatLit,
}
import core/state.{type Error}
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import syntax/formatter
import syntax/grammar.{
  type ParseResult, ParseError, ParseResult, type Span, type Value, AstValue, ListValue, TokenValue, alt, ref, rule, seq, many,
  token_pattern,
}
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
  /// Constructor with arg: #Some(42), #True(Unit)
  NCtr(tag: String, arg: NamedTerm, span: Span)
  /// Unit value
  NUnit(span: Span)
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
  /// Fixpoint for recursion: fix name -> body
  NFix(name: String, body: NamedTerm, span: Span)
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
  /// Constructor pattern with arg: #Some(n), #True(Unit)
  NPCtr(tag: String, arg: NamedPattern, span: Span)
  /// Unit pattern
  NPUnit(span: Span)
}

/// Case in match expression
pub type NamedCase {
  NCase(
    pattern: NamedPattern,
    body: NamedTerm,
    guard: Option(NamedTerm),
    span: Span,
  )
}

// ============================================================================
// PARSE VALUE TYPE
// ============================================================================
/// Wrapper type to allow grammar rules to return different types.
/// Some rules return NamedTerm, others return List(#(String, NamedTerm)) for field lists.
pub type ParseValue {
  AsCoreTerm(NamedTerm)
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
        Ok(index) -> Var(index, span)
        Error(_) -> Var(0, span)
        // Free variable
      }
    }
    NLit(value, span) -> Lit(value, span)
    NLam(name, body, span) -> {
      let body_db = named_to_de_bruijn_loop(body, [name, ..env])
      Lam([], #(name, Hole(-1, span)), body_db, span)
    }
    NPi(name, in_type, out_type, span) -> {
      let in_db = named_to_de_bruijn_loop(in_type, env)
      let out_db = named_to_de_bruijn_loop(out_type, [name, ..env])
      Pi([], name, in_db, out_db, span)
    }
    NApp(fun, arg, span) -> {
      let fun_db = named_to_de_bruijn_loop(fun, env)
      let arg_db = named_to_de_bruijn_loop(arg, env)
      App(fun_db, [], arg_db, span)
    }
    NAnn(term, typ, span) -> {
      let term_db = named_to_de_bruijn_loop(term, env)
      let typ_db = named_to_de_bruijn_loop(typ, env)
      Ann(term_db, typ_db, span)
    }
    NDot(arg, field, span) -> {
      let arg_db = named_to_de_bruijn_loop(arg, env)
      Dot(arg_db, field, span)
    }
    NCtr(tag, arg, span) -> {
      let arg_db = named_to_de_bruijn_loop(arg, env)
      Ctr(tag, arg_db, span)
    }
    NUnit(span) -> Unit(span)
    NTyp(level, span) -> Typ(level, span)
    NHole(id, span) -> Hole(id, span)
    NLitT(typ, span) -> LitT(typ, span)
    NRcd(fields, span) -> {
      let fields_db =
        fields
        |> list.map(fn(f) {
          let #(name, value) = f
          #(name, named_to_de_bruijn_loop(value, env))
        })
      Rcd(fields_db, span)
    }
    NMatch(arg, motive, cases, span) -> {
      let arg_db = named_to_de_bruijn_loop(arg, env)
      let motive_db = named_to_de_bruijn_loop(motive, env)
      let cases_db =
        cases |> list.map(fn(c) { named_case_to_de_bruijn(c, env) })
      Match(arg_db, motive_db, cases_db, span)
    }
    NCall(name, args, span) -> {
      let args_db = args |> list.map(fn(a) { named_to_de_bruijn_loop(a, env) })
      Call(name, args_db, span)
    }
    NComptime(term, span) -> {
      let term_db = named_to_de_bruijn_loop(term, env)
      Comptime(term_db, span)
    }
    NFix(name, body, span) -> {
      let body_db = named_to_de_bruijn_loop(body, [name, ..env])
      Fix(name, body_db, span)
    }
    NErr(message, span) -> {
      Err(message, span)
    }
  }
}

/// Convert NamedCase to Case with De Bruijn indices.
fn named_case_to_de_bruijn(named_case: NamedCase, env: List(String)) -> Case {
  let NCase(pattern, body, guard, span) = named_case
  let pattern_db = named_pattern_to_de_bruijn(pattern)
  let body_db = named_to_de_bruijn_loop(body, env)
  let guard_db = case guard {
    Some(g) -> Some(named_to_de_bruijn_loop(g, env))
    None -> None
  }
  Case(pattern_db, body_db, guard_db, span)
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
      let fields_db =
        fields
        |> list.map(fn(f) {
          let #(name, pat) = f
          #(name, named_pattern_to_de_bruijn(pat))
        })
      PRcd(fields_db)
    }
    NPCtr(tag, arg, _span) -> {
      let arg_db = named_pattern_to_de_bruijn(arg)
      PCtr(tag, arg_db)
    }
    NPUnit(_span) -> PUnit
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

pub fn parse(source: String) -> ParseResult(Term) {
  // Create an error placeholder AST to use if parsing fails
  let error_ast = AsCoreTerm(NErr("Parse error", grammar.Span("", 0, 0, 0, 0)))
  let parsed: ParseResult(ParseValue) =
    grammar.parse(core_grammar(), source, error_ast)
  case parsed {
    ParseResult(ast: ast, errors: errors) -> {
      case ast {
        AsCoreTerm(NErr(msg, _)) -> {
          // Got error AST from grammar.parse - include the message
          let placeholder =
            Err("Parse error: " <> msg, grammar.Span("", 0, 0, 0, 0))
          ParseResult(ast: placeholder, errors: errors)
        }
        AsCoreTerm(named_term) -> {
          // Got normal AST - check for errors
          case errors {
            [_, ..] -> {
              // Has errors - return error AST with error list
              let placeholder =
                
                  ast.Err("Parse error: see errors list",
                  grammar.Span("", 0, 0, 0, 0),
                )
              ParseResult(ast: placeholder, errors: errors)
            }
            [] -> {
              // No errors - process the AST
              let term = named_to_de_bruijn(named_term)
              ParseResult(ast: term, errors: [])
            }
          }
        }
        AsFields(_) -> {
          let placeholder =
            
              ast.Err("Expected expression, got field list",
              grammar.Span("", 0, 0, 0, 0),
            )
          ParseResult(ast: placeholder, errors: [
            ParseError(span: grammar.Span("", 0, 0, 0, 0), expected: "expression", got: "field list", context: ""),
          ])
        }
        AsCases(_) -> {
          let placeholder =
            
              ast.Err("Expected expression, got case list",
              grammar.Span("", 0, 0, 0, 0),
            )
          ParseResult(ast: placeholder, errors: [
            ParseError(span: grammar.Span("", 0, 0, 0, 0), expected: "expression", got: "case list", context: ""),
          ])
        }
        AsPattern(_) -> {
          let placeholder =
            
              ast.Err("Expected expression, got pattern",
              grammar.Span("", 0, 0, 0, 0),
            )
          ParseResult(ast: placeholder, errors: [
            ParseError(span: grammar.Span("", 0, 0, 0, 0), expected: "expression", got: "pattern", context: ""),
          ])
        }
        AsArgs(_) -> {
          let placeholder =
            
              ast.Err("Expected expression, got argument list",
              grammar.Span("", 0, 0, 0, 0),
            )
          ParseResult(ast: placeholder, errors: [
            ParseError(span: grammar.Span("", 0, 0, 0, 0), expected: "expression", got: "argument list", context: ""),
          ])
        }
      }
    }
  }
}

pub fn format(term: Term) -> String {
  format_term(term, -1, []) |> formatter.render_default
}

/// Format a term inline (for use in implicit args, etc.)
fn format_inline(term: Term) -> String {
  format_term(term, 100, []) |> formatter.render_default
}

// ============================================================================
// GRAMMAR DEFINITION
// ============================================================================

pub fn core_grammar() -> grammar.Grammar(ParseValue) {
  grammar.Grammar(
    name: "Core",
    start: "Expr",
    tokens: [
      "Ident",
      "Number",
      "LParen",
      "RParen",
      "LBrace",
      "RBrace",
      "Dot",
      "Operator",
      "Keyword",
      "Colon",
      "Equal",
      "Comma",
      "Arrow",
      "Hash",
      "Question",
      "Underscore",
      "At",
      "Percent",
      "PercentType",
      "PercentI32",
      "PercentI64",
      "PercentU32",
      "PercentU64",
      "PercentF32",
      "PercentF64",
      "PercentMatch",
      "PercentCall",
      "PercentComptime",
      "PercentLet",
      "PercentFix",
      "PercentDef",
      "Tilde",
      "Pipe",
      "In",
      "Rec",
    ],
    keywords: [],
    operators: [],
    rules: [
      // Main expression rule (lowest precedence first)
      rule("Expr", [
        // Keywords first (%match, %call, %comptime, %let, %fix) - these start with % tokens
        alt(ref("Match"), unwrap),
        alt(ref("Call"), unwrap),
        alt(ref("Comptime"), unwrap),
        alt(ref("Let"), unwrap),
        alt(ref("Fix"), unwrap),
        // Then other expressions
        alt(ref("Lambda"), unwrap),
        alt(ref("Pi"), unwrap),
        alt(ref("Ann"), unwrap),
        alt(ref("Dot"), unwrap),
        alt(ref("App"), unwrap),
        alt(ref("Atom"), unwrap),
      ]),
      // Lambda: x -> body or \x -> body
      rule("Lambda", [
        // \x -> body (backslash lambda)
        alt(
          seq([
            token_pattern("Backslash"),
            token_pattern("Ident"),
            token_pattern("Arrow"),
            ref("Expr"),
          ]),
          make_lambda,
        ),
        // x -> body (identifier lambda)
        alt(
          seq([
            token_pattern("Ident"),
            token_pattern("Arrow"),
            ref("Expr"),
          ]),
          make_lambda,
        ),
      ]),
      // Pi type: (x : A) -> B
      rule("Pi", [
        alt(
          seq([
            token_pattern("LParen"),
            token_pattern("Ident"),
            token_pattern("Colon"),
            ref("Expr"),
            token_pattern("RParen"),
            token_pattern("Arrow"),
            ref("Expr"),
          ]),
          make_pi,
        ),
      ]),
      // Type annotation: expr : Type
      rule("Ann", [
        alt(
          seq([
            ref("App"),
            token_pattern("Colon"),
            ref("Expr"),
          ]),
          make_annotation,
        ),
      ]),
      // Application: f(x) or f(x)(y) - left associative via iteration
      rule("App", [
        alt(
          seq([
            ref("Atom"),
            many(seq([
              token_pattern("LParen"),
              ref("Expr"),
              token_pattern("RParen"),
            ])),
          ]),
          fn(values) {
            // values = [Atom, ...] where ... could be ListValue or individual items
            case values {
              [first, ListValue(app_lists), ..] -> {
                // many() matched at least once
                let base = case first {
                  AstValue(b) -> b
                  _ -> panic as "Expected Atom"
                }
                fold_apps(base, app_lists)
              }
              [first, ..rest] -> {
                // many() matched but returned items directly (flattened)
                let base = case first {
                  AstValue(b) -> b
                  _ -> panic as "Expected Atom"
                }
                fold_apps(base, rest)
              }
              [first] -> {
                // No applications, just the atom
                case first {
                  AstValue(b) -> b
                  _ -> panic as "Expected Atom"
                }
              }
              _ -> panic as "Expected Atom and optional apps"
            }
          },
        ),
      ]),
      // Field access: expr.field
      rule("Dot", [
        alt(
          seq([
            ref("App"),
            token_pattern("Dot"),
            token_pattern("Ident"),
          ]),
          make_field_access,
        ),
        // Also allow field access on atoms (variables, records, etc.)
        alt(
          seq([
            ref("Atom"),
            token_pattern("Dot"),
            token_pattern("Ident"),
          ]),
          make_field_access,
        ),
      ]),
      // Match: %match arg ~ motive { | pat -> body ... }
      rule("Match", [
        alt(
          seq([
            token_pattern("PercentMatch"),
            ref("Expr"),
            token_pattern("Tilde"),
            ref("Expr"),
            token_pattern("LBrace"),
            ref("Cases"),
            token_pattern("RBrace"),
          ]),
          make_match,
        ),
      ]),
      // Call: %call name(args)
      rule("Call", [
        alt(
          seq([
            token_pattern("PercentCall"),
            token_pattern("Ident"),
            // Simple function name for now
            token_pattern("LParen"),
            ref("ArgList"),
            token_pattern("RParen"),
          ]),
          make_call,
        ),
      ]),
      // Comptime: %comptime term
      rule("Comptime", [
        alt(
          seq([
            token_pattern("PercentComptime"),
            ref("Expr"),
          ]),
          make_comptime,
        ),
      ]),
      // Let: %let [rec] name = value in body
      rule("Let", [
        // %let rec name = value in body
        alt(
          seq([
            token_pattern("PercentLet"),
            token_pattern("Rec"),
            token_pattern("Ident"),
            token_pattern("Equal"),
            ref("Expr"),
            token_pattern("In"),
            ref("Expr"),
          ]),
          make_let_rec,
        ),
        // %let name = value in body (without rec)
        alt(
          seq([
            token_pattern("PercentLet"),
            token_pattern("Ident"),
            token_pattern("Equal"),
            ref("Expr"),
            token_pattern("In"),
            ref("Expr"),
          ]),
          make_let,
        ),
      ]),
      // Fix: %fix name = term (fixpoint operator for recursion)
      rule("Fix", [
        alt(
          seq([
            token_pattern("PercentFix"),
            token_pattern("Ident"),
            token_pattern("Equal"),
            ref("Expr"),
          ]),
          make_fix,
        ),
      ]),
      // Atoms - the building blocks
      rule("Atom", [
        // Constructor with args: #Name(arg)
        alt(
          seq([
            token_pattern("Hash"),
            token_pattern("Ident"),
            token_pattern("LParen"),
            ref("Expr"),
            token_pattern("RParen"),
          ]),
          make_constructor_app,
        ),
        // Constructor without args: #Name
        alt(
          seq([
            token_pattern("Hash"),
            token_pattern("Ident"),
          ]),
          make_constructor,
        ),
        // Type universe with level: %Type(1)
        alt(
          seq([
            token_pattern("PercentType"),
            token_pattern("LParen"),
            token_pattern("Number"),
            token_pattern("RParen"),
          ]),
          make_typ_with_level,
        ),
        // Type universe without level: %Type
        alt(
          seq([
            token_pattern("PercentType"),
          ]),
          make_typ,
        ),
        // Literal types: %I32, %I64, %U32, %U64, %F32, %F64
        alt(token_pattern("PercentI32"), make_i32_type),
        alt(token_pattern("PercentI64"), make_i64_type),
        alt(token_pattern("PercentU32"), make_u32_type),
        alt(token_pattern("PercentU64"), make_u64_type),
        alt(token_pattern("PercentF32"), make_f32_type),
        alt(token_pattern("PercentF64"), make_f64_type),
        // Hole with id: ?1
        alt(
          seq([
            token_pattern("Question"),
            token_pattern("Number"),
          ]),
          make_hole_with_id,
        ),
        // Hole without id: ?
        alt(token_pattern("Question"), make_hole),
        // Empty record: {}
        alt(
          seq([
            token_pattern("LBrace"),
            token_pattern("RBrace"),
          ]),
          make_empty_record,
        ),
        // Variable
        alt(token_pattern("Ident"), make_var),
        // Number literal
        alt(token_pattern("Number"), make_literal),
        // Parenthesized expression
        alt(
          seq([
            token_pattern("LParen"),
            ref("Expr"),
            token_pattern("RParen"),
          ]),
          unwrap_parens,
        ),
        // Record with fields: {x: 1, y: 2}
        alt(
          seq([
            token_pattern("LBrace"),
            ref("FieldList"),
            token_pattern("RBrace"),
          ]),
          make_record_with_fields,
        ),
      ]),
      // Field list: x: expr, y: expr (returns AsFields)
      rule("FieldList", [
        // Multiple fields: x: expr, rest... (try this first for longest match)
        alt(
          seq([
            token_pattern("Ident"),
            token_pattern("Colon"),
            ref("Expr"),
            token_pattern("Comma"),
            ref("FieldList"),
          ]),
          make_field_cons,
        ),
        // Single field: x: expr
        alt(
          seq([
            token_pattern("Ident"),
            token_pattern("Colon"),
            ref("Expr"),
          ]),
          make_single_field,
        ),
      ]),
      // Cases: one or more | pattern [? guard] -> body
      rule("Cases", [
        // Multiple cases: | pat [? guard] -> body | pat [? guard] -> body ...
        alt(
          seq([
            ref("Case"),
            ref("Cases"),
          ]),
          make_cases_cons,
        ),
        // Single case: | pat [? guard] -> body
        alt(ref("Case"), unwrap_cases),
      ]),
      // Case: | pattern [? guard] -> body
      rule("Case", [
        // Case with guard: | pattern ? guard -> body
        alt(
          seq([
            token_pattern("Pipe"),
            ref("Pattern"),
            token_pattern("Question"),
            ref("Expr"),
            token_pattern("Arrow"),
            ref("Expr"),
          ]),
          make_case_with_guard,
        ),
        // Case without guard: | pattern -> body
        alt(
          seq([
            token_pattern("Pipe"),
            ref("Pattern"),
            token_pattern("Arrow"),
            ref("Expr"),
          ]),
          make_single_case,
        ),
      ]),
      // Pattern: x, _, x @ pat, %Type, 42, %I32, {fields}, #Name(pat)
      rule("Pattern", [
        // Variable pattern: x
        alt(token_pattern("Ident"), make_pattern_var),
        // Wildcard: _
        alt(token_pattern("Underscore"), make_pattern_any),
        // As-pattern: x @ pat
        alt(
          seq([
            token_pattern("Ident"),
            token_pattern("At"),
            ref("Pattern"),
          ]),
          make_pattern_as,
        ),
        // Constructor pattern with arg: #Name(pat)
        alt(
          seq([
            token_pattern("Hash"),
            token_pattern("Ident"),
            token_pattern("LParen"),
            ref("Pattern"),
            token_pattern("RParen"),
          ]),
          make_pattern_ctr_app,
        ),
        // Nullary constructor pattern: #Name
        alt(
          seq([
            token_pattern("Hash"),
            token_pattern("Ident"),
          ]),
          make_pattern_ctr,
        ),
        // Literal pattern: 42
        alt(token_pattern("Number"), make_pattern_lit),
      ]),
      // Argument list: expr, expr, ...
      rule("ArgList", [
        // Single arg
        alt(seq([ref("Expr")]), make_single_arg),
        // Multiple args: expr, args...
        alt(
          seq([
            ref("Expr"),
            token_pattern("Comma"),
            ref("ArgList"),
          ]),
          make_arg_cons,
        ),
      ]),
    ],
  )
}

// ============================================================================
// CONSTRUCTOR HELPERS
// ============================================================================

fn unwrap(values) -> ParseValue {
  case values {
    [AstValue(AsCoreTerm(term))] -> AsCoreTerm(term)
    _ -> panic as "Expected single NamedTerm value"
  }
}

fn unwrap_cases(values) -> ParseValue {
  case values {
    [AstValue(AsCases(cases))] -> AsCases(cases)
    _ -> panic as "Expected single Cases value"
  }
}

fn make_cases_cons(values) -> ParseValue {
  case values {
    [AstValue(AsCases(first)), AstValue(AsCases(rest))] ->
      AsCases(list.append(first, rest))
    _ -> panic as "Expected cases cons"
  }
}

fn unwrap_parens(values) -> ParseValue {
  case values {
    [_, AstValue(AsCoreTerm(term)), _] -> AsCoreTerm(term)
    _ -> panic as "Expected (expr)"
  }
}

fn make_lambda(values) -> ParseValue {
  case values {
    [TokenValue(name_token), _, AstValue(AsCoreTerm(body))] ->
      AsCoreTerm(NLam(
        name_token.value,
        body,
        grammar.span_from_token(name_token, "input")
      ))
    _ -> panic as "Expected lambda (x -> body)"
  }
}

fn make_pi(values) -> ParseValue {
  case values {
    [
      _,
      TokenValue(name_token),
      _,
      AstValue(AsCoreTerm(in_term)),
      _,
      _,
      AstValue(AsCoreTerm(out_term)),
    ] -> AsCoreTerm(NPi(name_token.value, in_term, out_term, get_span(in_term)))
    _ -> panic as "Expected Pi type ((x : A) -> B)"
  }
}

fn make_annotation(values) -> ParseValue {
  case values {
    [AstValue(AsCoreTerm(term)), _, AstValue(AsCoreTerm(typ))] ->
      AsCoreTerm(NAnn(term, typ, get_span(term)))
    _ -> panic as "Expected annotation (term : type)"
  }
}

fn make_application(values) -> ParseValue {
  case values {
    [AstValue(AsCoreTerm(fun)), _, AstValue(AsCoreTerm(arg)), _] ->
      AsCoreTerm(NApp(
        fun,
        arg,
        grammar.span_from_token(values |> get_first_token, "input"),
      ))
    _ -> panic as "Expected f(args)"
  }
}

fn fold_apps(base, app_values) -> ParseValue {
  // app_values is a flat list: [LParen, Expr, RParen, LParen, Expr, RParen, ...]
  case app_values {
    [_, AstValue(AsCoreTerm(arg)), _, ..rest] -> {
      let new_app = AsCoreTerm(NApp(
        case base {
          AsCoreTerm(t) -> t
          _ -> panic as "Expected core term"
        },
        arg,
        grammar.Span("input", 0, 0, 0, 0),
      ))
      fold_apps(new_app, rest)
    }
    [] -> base
    _ -> panic as "Expected application args"
  }
}

fn make_field_access(values) -> ParseValue {
  case values {
    [AstValue(AsCoreTerm(arg)), _, TokenValue(field_token)] ->
      AsCoreTerm(NDot(arg, field_token.value, get_span(arg)))
    _ -> panic as "Expected field access (expr.field)"
  }
}

fn make_empty_record(values) -> ParseValue {
  case values {
    [_, _] ->
      AsCoreTerm(NRcd(
        [],
        grammar.span_from_token(values |> get_first_token, "input"),
      ))
    _ -> panic as "Expected empty record {}"
  }
}

fn make_var(values) -> ParseValue {
  case values {
    [TokenValue(token)] ->
      AsCoreTerm(NVar(token.value, grammar.span_from_token(token, "input")))
    _ -> panic as "Expected identifier"
  }
}

fn make_literal(values) -> ParseValue {
  case values {
    [TokenValue(token)] -> {
      case int.parse(token.value) {
        Ok(n) -> AsCoreTerm(NLit(I32(n), grammar.span_from_token(token, "input")))
        Error(_) ->
          AsCoreTerm(NLit(I32(0), grammar.span_from_token(token, "input")))
      }
    }
    _ -> panic as "Expected number token"
  }
}

fn make_hole(values) -> ParseValue {
  case values {
    [TokenValue(token)] -> {
      case token.value {
        "?" -> AsCoreTerm(NHole(0, grammar.span_from_token(token, "input")))
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
        Ok(id) -> AsCoreTerm(NHole(id, grammar.span_from_token(id_token, "input")))
        Error(_) -> AsCoreTerm(NHole(0, grammar.span_from_token(id_token, "input")))
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
        "Type" -> AsCoreTerm(NTyp(0, grammar.span_from_token(token, "input")))
        "I32" -> AsCoreTerm(NLitT(I32T, grammar.span_from_token(token, "input")))
        "I64" -> AsCoreTerm(NLitT(I64T, grammar.span_from_token(token, "input")))
        "F32" -> AsCoreTerm(NLitT(F32T, grammar.span_from_token(token, "input")))
        "F64" -> AsCoreTerm(NLitT(F64T, grammar.span_from_token(token, "input")))
        "U32" -> AsCoreTerm(NLitT(U32T, grammar.span_from_token(token, "input")))
        "U64" -> AsCoreTerm(NLitT(U64T, grammar.span_from_token(token, "input")))
        // Otherwise it's a constructor-like type
        _ ->
          AsCoreTerm(NCtr(
            token.value,
            NHole(0, grammar.span_from_token(token, "input")),
            grammar.span_from_token(token, "input"),
          ))
      }
    }
    _ -> panic as "Expected %Type or %I32"
  }
}

fn make_typ_with_level(values) -> ParseValue {
  case values {
    [TokenValue(type_token), _, TokenValue(level_token), _] -> {
      case type_token.value {
        "%Type" -> {
          case int.parse(level_token.value) {
            Ok(level) ->
              AsCoreTerm(NTyp(level, grammar.span_from_token(type_token, "input")))
            Error(_) ->
              AsCoreTerm(NTyp(0, grammar.span_from_token(type_token, "input")))
          }
        }
        _ -> panic as "Expected %Type(n)"
      }
    }
    _ -> panic as "Expected %Type(n)"
  }
}

fn make_typ(values) -> ParseValue {
  case values {
    [TokenValue(token)] ->
      AsCoreTerm(NTyp(0, grammar.span_from_token(token, "input")))
    _ -> panic as "Expected %Type"
  }
}

fn make_i32_type(values) -> ParseValue {
  case values {
    [TokenValue(token)] ->
      AsCoreTerm(NLitT(I32T, grammar.span_from_token(token, "input")))
    _ -> panic as "Expected %I32"
  }
}

fn make_i64_type(values) -> ParseValue {
  case values {
    [TokenValue(token)] ->
      AsCoreTerm(NLitT(I64T, grammar.span_from_token(token, "input")))
    _ -> panic as "Expected %I64"
  }
}

fn make_u32_type(values) -> ParseValue {
  case values {
    [TokenValue(token)] ->
      AsCoreTerm(NLitT(U32T, grammar.span_from_token(token, "input")))
    _ -> panic as "Expected %U32"
  }
}

fn make_u64_type(values) -> ParseValue {
  case values {
    [TokenValue(token)] ->
      AsCoreTerm(NLitT(U64T, grammar.span_from_token(token, "input")))
    _ -> panic as "Expected %U64"
  }
}

fn make_f32_type(values) -> ParseValue {
  case values {
    [TokenValue(token)] ->
      AsCoreTerm(NLitT(F32T, grammar.span_from_token(token, "input")))
    _ -> panic as "Expected %F32"
  }
}

fn make_f64_type(values) -> ParseValue {
  case values {
    [TokenValue(token)] ->
      AsCoreTerm(NLitT(F64T, grammar.span_from_token(token, "input")))
    _ -> panic as "Expected %F64"
  }
}

fn make_constructor(values) -> ParseValue {
  case values {
    [_, TokenValue(token)] -> {
      let span = grammar.span_from_token(token, "input")
      AsCoreTerm(NCtr(token.value, NUnit(span), span))
    }
    _ -> panic as "Expected constructor (#Name)"
  }
}

fn make_constructor_app(values) -> ParseValue {
  case values {
    [_, TokenValue(name_token), _, AstValue(AsCoreTerm(arg)), _] ->
      AsCoreTerm(NCtr(
        name_token.value,
        arg,
        grammar.span_from_token(name_token, "input")
      ))
    _ -> panic as "Expected constructor application (#Name(arg))"
  }
}

fn make_record_with_fields(values) -> ParseValue {
  case values {
    [_, AstValue(AsFields(fields)), _] ->
      AsCoreTerm(NRcd(
        fields,
        grammar.span_from_token(values |> get_first_token, "input"),
      ))
    _ -> panic as "Expected record with fields {x: 1, ...}"
  }
}

fn make_single_field(values) -> ParseValue {
  case values {
    [TokenValue(name_token), _, AstValue(AsCoreTerm(value))] ->
      AsFields([#(name_token.value, value)])
    _ -> panic as "Expected single field (name: value)"
  }
}

fn make_field_cons(values) -> ParseValue {
  case values {
    [
      TokenValue(name_token),
      _,
      AstValue(AsCoreTerm(value)),
      _,
      AstValue(AsFields(rest)),
    ] -> AsFields([#(name_token.value, value), ..rest])
    _ -> panic as "Expected field list (name: value, ...)"
  }
}

// Match, Call, Comptime constructors
fn make_match(values) -> ParseValue {
  case values {
    [
      _,
      AstValue(AsCoreTerm(arg)),
      _,
      AstValue(AsCoreTerm(motive)),
      _,
      AstValue(AsCases(cases)),
      _,
    ] -> AsCoreTerm(NMatch(arg, motive, cases, get_span(arg)))
    _ -> panic as "Expected match expression"
  }
}

fn make_call(values) -> ParseValue {
  case values {
    [_, AstValue(AsCoreTerm(name_term)), _, AstValue(AsArgs(args)), _] -> {
      // Extract name from the term (could be NVar, NDot, etc.)
      let name = term_to_name(name_term)
      AsCoreTerm(NCall(name, args, get_span(name_term)))
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
    [_, AstValue(AsCoreTerm(term))] ->
      AsCoreTerm(NComptime(
        term,
        grammar.span_from_token(values |> get_first_token, "input"),
      ))
    _ -> panic as "Expected comptime expression"
  }
}

fn make_let(values) -> ParseValue {
  case values {
    [
      _,
      TokenValue(name_token),
      _,
      AstValue(AsCoreTerm(value)),
      _,
      AstValue(AsCoreTerm(body)),
    ] -> {
      // Desugar: let name = value in body  →  (name -> body)(value)
      let name = name_token.value
      let span = grammar.span_from_token(name_token, "input")
      let lambda = NLam(name, body, span)
      let app = NApp(lambda, value, span)
      AsCoreTerm(app)
    }
    _ -> panic as "Expected let binding"
  }
}

fn make_let_rec(values) -> ParseValue {
  case values {
    [
      _,
      _,
      TokenValue(name_token),
      _,
      AstValue(AsCoreTerm(value)),
      _,
      AstValue(AsCoreTerm(body)),
    ] -> {
      // let rec name = value in body
      // For recursion, we need to allow name to appear in value
      // Desugar to: let name = (fix -> value)(name) in body
      // For now, just use regular let desugaring (type checker will need to handle recursion)
      let name = name_token.value
      let span = grammar.span_from_token(name_token, "input")
      let lambda = NLam(name, body, span)
      let app = NApp(lambda, value, span)
      AsCoreTerm(app)
    }
    _ -> panic as "Expected let rec binding"
  }
}

fn make_fix(values) -> ParseValue {
  case values {
    [_, TokenValue(name_token), _, AstValue(AsCoreTerm(body))] -> {
      let name = name_token.value
      AsCoreTerm(NFix(name, body, grammar.span_from_token(name_token, "input")))
    }
    _ -> panic as "Expected fix expression"
  }
}

// Cases constructors
fn make_case_with_guard(values) -> ParseValue {
  case values {
    [
      _,
      AstValue(AsPattern(pattern)),
      _,
      AstValue(AsCoreTerm(guard)),
      _,
      AstValue(AsCoreTerm(body)),
    ] -> AsCases([NCase(pattern, body, Some(guard), get_span(body))])
    _ -> panic as "Expected case with guard"
  }
}

fn make_single_case(values) -> ParseValue {
  case values {
    [_, AstValue(AsPattern(pattern)), _, AstValue(AsCoreTerm(body))] ->
      AsCases([NCase(pattern, body, None, get_span(body))])
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
    [TokenValue(token)] ->
      AsPattern(NPAny(grammar.span_from_token(token, "input")))
    _ -> panic as "Expected wildcard pattern"
  }
}

fn make_pattern_as(values) -> ParseValue {
  case values {
    [TokenValue(name_token), _, AstValue(AsPattern(pattern))] ->
      AsPattern(NPAs(
        pattern,
        name_token.value,
        grammar.span_from_token(name_token, "input")
      ))
    _ -> panic as "Expected as-pattern"
  }
}

fn make_pattern_ctr_app(values) -> ParseValue {
  case values {
    [_, TokenValue(tag_token), _, _, AstValue(AsPattern(arg)), _] ->
      AsPattern(NPCtr(
        tag_token.value,
        arg,
        grammar.span_from_token(tag_token, "input"),
      ))
    _ -> panic as "Expected constructor pattern"
  }
}

fn make_pattern_ctr(values) -> ParseValue {
  case values {
    [_, TokenValue(tag_token)] ->
      AsPattern(NPCtr(
        tag_token.value,
        NPUnit(grammar.span_from_token(tag_token, "input")),
        grammar.span_from_token(tag_token, "input"),
      ))
    _ -> panic as "Expected nullary constructor pattern"
  }
}

fn make_pattern_lit(values) -> ParseValue {
  case values {
    [TokenValue(token)] -> {
      case int.parse(token.value) {
        Ok(n) ->
          AsPattern(NPLit(I32(n), grammar.span_from_token(token, "input")))
        Error(_) ->
          AsPattern(NPLit(I32(0), grammar.span_from_token(token, "input")))
      }
    }
    _ -> panic as "Expected literal pattern"
  }
}

// ArgList constructors
fn make_single_arg(values) -> ParseValue {
  case values {
    [AstValue(AsCoreTerm(arg))] -> AsArgs([arg])
    _ -> panic as "Expected single argument"
  }
}

fn make_arg_cons(values) -> ParseValue {
  case values {
    [AstValue(AsCoreTerm(arg)), _, AstValue(AsArgs(rest))] -> AsArgs([arg, ..rest])
    _ -> panic as "Expected argument list"
  }
}

fn get_first_token(values: List(grammar.Value(ParseValue))) -> Token {
  case values {
    [TokenValue(token), ..] -> token
    [AstValue(AsCoreTerm(term)), ..] -> {
      get_span(term) |> span_to_token
    }
    _ -> panic as "Expected at least one value"
  }
}

fn span_to_token(span: Span) -> Token {
  lexer.Token(
    "Unknown",
    "",
    span.start_line,
    span.end_col,
    span.start_line,
    span.start_col,
  )
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
    NUnit(span) -> span
    NTyp(_, span) -> span
    NHole(_, span) -> span
    NLitT(_, span) -> span
    NRcd(_, span) -> span
    NMatch(_, _, _, span) -> span
    NCall(_, _, span) -> span
    NComptime(_, span) -> span
    NFix(_, _, span) -> span
    NErr(_, span) -> span
  }
}

// ============================================================================
// FORMATTER
// ============================================================================

fn format_value(value: ParseValue, parent_prec: Int) -> formatter.Doc {
  case value {
    AsCoreTerm(named_term) -> {
      let term = named_to_de_bruijn(named_term)
      format_term(term, parent_prec, [])
    }
    AsFields(_) -> formatter.text("<fields>")
    AsCases(_) -> formatter.text("<cases>")
    AsPattern(_) -> formatter.text("<pattern>")
    AsArgs(_) -> formatter.text("<args>")
  }
}

fn format_term(
  term: Term,
  parent_prec: Int,
  bindings: List(String),
) -> formatter.Doc {
  case term {
    Var(index, _) -> {
      case get_binding(bindings, index) {
        Ok(name) -> formatter.text(name)
        Error(_) ->
          formatter.concat([
            formatter.text("var"),
            formatter.text(int.to_string(index)),
          ])
      }
    }
    Lit(value, _) -> {
      case value {
        I32(n) -> formatter.text(int.to_string(n))
        I64(n) ->
          formatter.concat([
            formatter.text(int.to_string(n)),
            formatter.text("i64"),
          ])
        U32(n) ->
          formatter.concat([
            formatter.text(int.to_string(n)),
            formatter.text("u32"),
          ])
        U64(n) ->
          formatter.concat([
            formatter.text(int.to_string(n)),
            formatter.text("u64"),
          ])
        F32(f) -> formatter.text(float.to_string(f))
        F64(f) -> formatter.text(float.to_string(f))
        IntLit(n) -> formatter.text(int.to_string(n))
        FloatLit(f) -> formatter.text(float.to_string(f))
      }
    }
    Typ(level, _) -> {
      case level {
        0 -> formatter.text("%Type")
        _ ->
          formatter.concat([
            formatter.text("%Type("),
            formatter.text(int.to_string(level)),
            formatter.text(")"),
          ])
      }
    }
    Hole(id, _) -> {
      case id {
        0 -> formatter.text("?")
        _ ->
          formatter.concat([
            formatter.text("?"),
            formatter.text(int.to_string(id)),
          ])
      }
    }
    LitT(typ, _) -> {
      case typ {
        I32T -> formatter.text("%I32")
        I64T -> formatter.text("%I64")
        U32T -> formatter.text("%U32")
        U64T -> formatter.text("%U64")
        F32T -> formatter.text("%F32")
        F64T -> formatter.text("%F64")
        ILitT -> formatter.text("%Int")
        FLitT -> formatter.text("%Float")
      }
    }
    Ctr(tag, arg, _) -> {
      // Check if arg is a Hole or Typ(0) placeholder - if so, just show the tag
      case arg {
        Hole(_, _) -> formatter.concat([formatter.text("#"), formatter.text(tag)])
        Typ(0, _) -> formatter.concat([formatter.text("#"), formatter.text(tag)])
        Unit(_) -> formatter.concat([formatter.text("#"), formatter.text(tag)])
        _ ->
          formatter.concat([
            formatter.text("#"),
            formatter.text(tag),
            formatter.text("("),
            format_term(arg, 50, bindings),
            formatter.text(")"),
          ])
      }
    }
    Unit(_) -> formatter.text("Unit")
    Dot(arg, field, _) -> {
      let inner =
        formatter.concat([
          format_term(arg, 90, bindings),
          formatter.text("."),
          formatter.text(field),
        ])
      wrap_parens(inner, 90 < parent_prec)
    }
    Ann(term, typ, _) -> {
      let inner =
        formatter.concat([
          format_term(term, 50, bindings),
          formatter.text(" : "),
          format_term(typ, 50, bindings),
        ])
      wrap_parens(inner, 50 < parent_prec)
    }
    Pi(implicit, name, in_term, out_term, _) -> {
      let implicit_str = case implicit {
        [] -> ""
        _ -> "<" <> string.join(implicit, ", ") <> ">"
      }
      let inner =
        formatter.concat([
          formatter.text("%pi"),
          formatter.text(implicit_str),
          formatter.text("("),
          formatter.text(name),
          formatter.text(" : "),
          format_term(in_term, 50, bindings),
          formatter.text(") -> "),
          format_term(out_term, 65, [name, ..bindings]),
        ])
      wrap_parens(inner, 65 < parent_prec)
    }
    Rcd(fields, _) -> {
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
            list.intersperse(field_docs, formatter.text(", "))
              |> formatter.concat,
            formatter.text("}"),
          ])
        }
      }
    }
    Lam(implicit, param, body, _) -> {
      let #(name, _) = param
      let implicit_str = case implicit {
        [] -> ""
        _ -> "<" <> string.join(implicit, ", ") <> ">"
      }
      let inner =
        formatter.concat([
          formatter.text("%fn"),
          formatter.text(implicit_str),
          formatter.text("("),
          formatter.text(name),
          formatter.text(") -> "),
          format_term(body, 70, [name, ..bindings]),
        ])
      wrap_parens(inner, 70 < parent_prec)
    }
    App(fun, implicit, arg, _) -> {
      let implicit_str = case implicit {
        [] -> ""
        _ -> "<" <> string.join(list.map(implicit, format_inline), ", ") <> ">"
      }
      let inner =
        formatter.concat([
          format_term(fun, 85, bindings),
          formatter.text(implicit_str),
          formatter.text("("),
          format_term(arg, 85, bindings),
          formatter.text(")"),
        ])
      wrap_parens(inner, 85 < parent_prec)
    }
    Match(arg, motive, cases, _) -> {
      let case_docs =
        cases
        |> list.map(fn(c) {
          let Case(pattern, body, guard, _) = c
          let guard_doc = case guard {
            Some(g) ->
              formatter.concat([
                formatter.text(" ? "),
                format_term(g, 70, bindings),
              ])
            None -> formatter.text("")
          }
          formatter.concat([
            formatter.text("  | "),
            format_pattern(pattern),
            guard_doc,
            formatter.text(" -> "),
            format_term(body, 70, bindings),
          ])
        })
      let inner =
        formatter.concat([
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
    Call(name, args, _) -> {
      let arg_docs = args |> list.map(fn(a) { format_term(a, 85, bindings) })
      let inner =
        formatter.concat([
          formatter.text("%call "),
          formatter.text(name),
          formatter.text("("),
          list.intersperse(arg_docs, formatter.text(", ")) |> formatter.concat,
          formatter.text(")"),
        ])
      wrap_parens(inner, 85 < parent_prec)
    }
    Comptime(term, _) -> {
      let inner =
        formatter.concat([
          formatter.text("%comptime "),
          format_term(term, 50, bindings),
        ])
      wrap_parens(inner, 50 < parent_prec)
    }
    Fix(name, body, _) -> {
      let inner =
        formatter.concat([
          formatter.text("%fix "),
          formatter.text(name),
          formatter.text(" = "),
          format_term(body, 70, [name, ..bindings]),
        ])
      wrap_parens(inner, 70 < parent_prec)
    }
    Err(msg, _) ->
      formatter.concat([
        formatter.text("<error: "),
        formatter.text(msg),
        formatter.text(">"),
      ])
    ast.Let(name, value, body, _) -> {
      let inner =
        formatter.concat([
          formatter.text("let "),
          formatter.text(name),
          formatter.text(" = "),
          format_term(value, 70, bindings),
          formatter.text(" in"),
          formatter.line(),
          format_term(body, 70, [name, ..bindings]),
        ])
      wrap_parens(inner, 70 < parent_prec)
    }
  }
}

/// Format a pattern.
fn format_pattern(pattern: Pattern) -> formatter.Doc {
  case pattern {
    PAny -> formatter.text("_")
    PAs(inner, name) ->
      formatter.concat([
        formatter.text(name),
        formatter.text(" @ "),
        format_pattern(inner),
      ])
    PTyp(level) -> {
      case level {
        0 -> formatter.text("%Type")
        _ ->
          formatter.concat([
            formatter.text("%Type("),
            formatter.text(int.to_string(level)),
            formatter.text(")"),
          ])
      }
    }
    PLit(value) -> {
      case value {
        I32(n) -> formatter.text(int.to_string(n))
        I64(n) -> formatter.text(int.to_string(n))
        U32(n) -> formatter.text(int.to_string(n))
        U64(n) -> formatter.text(int.to_string(n))
        F32(f) -> formatter.text(float.to_string(f))
        F64(f) -> formatter.text(float.to_string(f))
        IntLit(n) -> formatter.text(int.to_string(n))
        FloatLit(f) -> formatter.text(float.to_string(f))
      }
    }
    PLitT(typ) -> {
      case typ {
        I32T -> formatter.text("%I32")
        I64T -> formatter.text("%I64")
        U32T -> formatter.text("%U32")
        U64T -> formatter.text("%U64")
        F32T -> formatter.text("%F32")
        F64T -> formatter.text("%F64")
        ILitT -> formatter.text("%Int")
        FLitT -> formatter.text("%Float")
      }
    }
    PRcd(fields) -> {
      let field_docs =
        fields
        |> list.map(fn(f) {
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
    PCtr(tag, arg) ->
      formatter.concat([
        formatter.text("#"),
        formatter.text(tag),
        formatter.text("("),
        format_pattern(arg),
        formatter.text(")"),
      ])
    PUnit ->
      formatter.text("Unit")
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

// ============================================================================
// TERM TO STRING (for golden file output)
// ============================================================================

/// Convert a Term to a readable string representation.
/// Used for displaying evaluation results in golden files.
pub fn term_to_string(term: Term) -> String {
  term_to_string_loop(term, [])
}

fn term_to_string_loop(term: Term, bindings: List(String)) -> String {
  let data = term
  case data {
    ast.Typ(k, _) -> "%Type" <> int.to_string(k)
    ast.Lit(literal, _) -> literal_to_string(literal)
    ast.LitT(literal_type, _) -> literal_type_to_string(literal_type)
    ast.Var(index, _) -> {
      case get_binding(bindings, index) {
        Ok(name) -> name
        Error(Nil) -> "var" <> int.to_string(index)
      }
    }
    ast.Hole(id, _) -> "?" <> int.to_string(id)
    ast.Err(msg, _) -> "Err(" <> msg <> ")"
    ast.Rcd(fields, _) -> {
      let field_strs = fields |> list.map(fn(f) { f.0 <> ": " <> term_to_string_loop(f.1, bindings) })
      "{" <> string.join(field_strs, ", ") <> "}"
    }
    ast.Ctr(tag, arg, _) -> "#" <> tag <> "(" <> term_to_string_loop(arg, bindings) <> ")"
    ast.Unit(_) -> "#Unit"
    ast.Dot(arg, field, _) -> term_to_string_loop(arg, bindings) <> "." <> field
    ast.Ann(term, typ, _) -> "(" <> term_to_string_loop(term, bindings) <> ": " <> term_to_string_loop(typ, bindings) <> ")"
    ast.Lam(implicit, param, body, _) -> {
      let #(name, _) = param
      let implicit_str = case implicit {
        [] -> ""
        _ -> "<" <> string.join(implicit, ", ") <> ">"
      }
      "%fn" <> implicit_str <> "(" <> name <> ") -> " <> term_to_string_loop(body, [name, ..bindings])
    }
    ast.Pi(implicit, name, in_ty, out_ty, _) -> {
      let implicit_str = case implicit {
        [] -> ""
        _ -> "<" <> string.join(implicit, ", ") <> ">"
      }
      "%pi" <> implicit_str <> "(" <> name <> ": " <> term_to_string_loop(in_ty, bindings) <> ") -> " <> term_to_string_loop(out_ty, [name, ..bindings])
    }
    ast.App(fun, implicit, arg, _) -> {
      let implicit_str = case implicit {
        [] -> ""
        _ -> "<" <> string.join(list.map(implicit, fn(t) { term_to_string_loop(t, bindings) }), ", ") <> ">"
      }
      term_to_string_loop(fun, bindings) <> implicit_str <> "(" <> term_to_string_loop(arg, bindings) <> ")"
    }
    ast.Match(arg, _motive, _cases, _) -> {
      "match(" <> term_to_string_loop(arg, bindings) <> ") { ... }"
    }
    ast.Call(name, args, _) -> {
      name <> "(" <> string.join(args |> list.map(fn(a) { term_to_string_loop(a, bindings) }), ", ") <> ")"
    }
    ast.Comptime(term, _) -> "comptime { " <> term_to_string_loop(term, bindings) <> " }"
    ast.Fix(name, body, _) -> "fix " <> name <> " -> " <> term_to_string_loop(body, [name, ..bindings])
    ast.Let(name, value, body, _) -> "let " <> name <> " = " <> term_to_string_loop(value, bindings) <> " in " <> term_to_string_loop(body, [name, ..bindings])
  }
}

fn literal_to_string(literal: ast.Literal) -> String {
  case literal {
    ast.I32(n) -> int.to_string(n)
    ast.I64(n) -> int.to_string(n)
    ast.U32(n) -> int.to_string(n)
    ast.U64(n) -> int.to_string(n)
    ast.F32(f) -> float_to_string(f)
    ast.F64(f) -> float_to_string(f)
    ast.IntLit(n) -> int.to_string(n)
    ast.FloatLit(f) -> float_to_string(f)
  }
}

fn literal_type_to_string(literal_type: ast.LiteralType) -> String {
  case literal_type {
    ast.I32T -> "%I32"
    ast.I64T -> "%I64"
    ast.U32T -> "%U32"
    ast.U64T -> "%U64"
    ast.F32T -> "%F32"
    ast.F64T -> "%F64"
    ast.ILitT -> "%Int"
    ast.FLitT -> "%Float"
  }
}

fn float_to_string(f: Float) -> String {
  // Simple float to string conversion
  case f {
    0.0 -> "0.0"
    1.0 -> "1.0"
    _ -> "float"
  }
}
