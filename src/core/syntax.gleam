/// Core Language Parser
///
/// Parses source strings into Core AST terms with De Bruijn indices.
///
/// Syntax:
///   - Variables: x, y, z
///   - Holes: ? or ?0, ?1
///   - Lambda: %fn(name: Type) => body
///   - Application: fun(fun_arg: arg)
///   - Pi type: %fn(name: Domain) -> Codomain
///   - Literals: 42, 3.14
///   - Constructors: #Tag, #Tag(arg)
///   - Match: %match arg { | pattern ? guard => body }
///   - Let: %let name = value; body
///   - Annotation: (term : Type)
///   - Unit: ()
///   - Type: %Type, %Type(1)
///   - Errors: %err("message")
///   - Records: {x: 1, y: 2}

import core/ast.{type Term, type Pattern, type Case,
  Var, Hole, Lam, App, Pi, Lit, Ctr, Match, Ann, Rcd, Typ, Err, let_var,
  Case as CoreCase, PAny, PVar, PCtr, PUnit, PLit, Int as LitInt, Float as LitFloat}
import syntax/base_lexer.{Token, type Token, tokenize}
import syntax/grammar.{type ParseError, ParseError}
import syntax/span.{type Span, single, merge, Span}
import gleam/list
import gleam/int
import gleam/float
import gleam/option.{Some, None}

/// Parse a Core source string into a Term.
pub fn parse(source: String) -> #(Term, List(ParseError)) {
  let tokens = tokenize(source)
  parse_tokens(tokens, "")
}

/// Parse tokens into a Core term.
pub fn parse_tokens(tokens: List(Token), filename: String) -> #(Term, List(ParseError)) {
  let state = #(tokens, 0, [], filename, [])
  let #(term, state2) = parse_term(state)
  let #(tokens2, pos2, _, _, errs) = state2
  case term {
    Err(msg, _) -> #(Err(msg, single(filename, 1, 1)), errs)
    t -> {
      let rest = try_peek(tokens2, pos2)
      case rest {
        Error(_) -> #(t, errs)
        Ok(Token(kind: "Eof", value: "", span: _)) -> #(t, errs)
        Ok(Token(value, _, span)) -> {
          let err = ParseError(span: span, expected: "end of input", got: value, context: "unexpected token")
          #(t, [err, ..errs])
        }
      }
    }
  }
}

type Parser = #(List(Token), Int, List(#(String, Int)), String, List(ParseError))

fn try_peek(tokens: List(Token), pos: Int) -> Result(Token, List(ParseError)) {
  case list.drop(tokens, pos) {
    [] -> Error([])
    [t, ..] -> Ok(t)
  }
}

fn add_binding(p: Parser, name: String) -> Parser {
  let #(tokens, pos, env, fn_, errors) = p
  let new_depth = list.length(env) + 1
  #(tokens, pos, [ #(name, new_depth), ..env ], fn_, errors)
}

fn current_span(p: Parser) -> Span {
  let #(tokens, pos, _, fn_, _) = p
  case list.drop(tokens, pos) {
    [] -> single(fn_, 1, 1)
    [Token(_, _, span), ..] -> span
  }
}

fn term_span(term: Term) -> Span {
  case term {
    Var(_, span) -> span
    Hole(_, span) -> span
    Lam(_, _, span) -> span
    App(_, _, span) -> span
    Pi(_, _, span) -> span
    Lit(_, span) -> span
    Ctr(_, _, span) -> span
    Match(_, _, span) -> span
    Ann(_, _, span) -> span
    Rcd(_, span) -> span
    Typ(_, span) -> span
    Err(_, span) -> span
  }
}

fn skip(kind: String, p: Parser) -> Parser {
  let #(tokens, pos, env, fn_, errors) = p
  case kind {
    "->" -> {
      case list.drop(tokens, pos) {
        [Token("Op", "-", _), Token("Op", ">", _), .._] -> #(tokens, pos + 2, env, fn_, errors)
        _ -> p
      }
    }
    "=>" -> {
      case list.drop(tokens, pos) {
        [Token("Punct", "=", _), Token("Op", ">", _), .._] -> #(tokens, pos + 2, env, fn_, errors)
        _ -> p
      }
    }
    _ -> {
      case list.drop(tokens, pos) {
        [Token(k, _, _), ..] if k == kind -> #(tokens, pos + 1, env, fn_, errors)
        [Token("Punct", pval, _), ..] if pval == kind -> #(tokens, pos + 1, env, fn_, errors)
        [Token("Op", opval, _), ..] if opval == kind -> #(tokens, pos + 1, env, fn_, errors)
        _ -> p
      }
    }
  }
}

fn expect_name_opt(p: Parser) -> #(String, Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [Token("Name", v, _), .._rest] -> #(v, #(tokens, pos + 1, env, fn_, errors))
    _ -> #("", p)
  }
}

fn parse_term(p: Parser) -> #(Term, Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  let span = current_span(p)
  case list.drop(tokens, pos) {
    [] -> { let e = Err("unexpected end of input", span)#(e, p) }
    
    // Integer and float literals
    [Token("Integer", v, _), .._] ->
      case int.parse(v) {
        Ok(value) -> #(Lit(LitInt(value), span), #(tokens, pos + 1, env, fn_, errors))
        Error(_) -> { let e = Err("invalid integer: " <> v, span)#(e, #(tokens, pos + 1, env, fn_, errors)) }
      }
    [Token("Float", v, _), .._] ->
      case float.parse(v) {
        Ok(value) -> #(Lit(LitFloat(value), span), #(tokens, pos + 1, env, fn_, errors))
        Error(_) -> { let e = Err("invalid float: " <> v, span)#(e, #(tokens, pos + 1, env, fn_, errors)) }
      }
    
    // String literals - error
    [Token("String", v, _), .._] -> {
      let e = Err("string literal not supported: " <> v, span)
      #(e, #(tokens, pos + 1, env, fn_, errors))
    }
    
    // Holes: ? or ?0, ?1
    [Token("Op", "?", _), ..rest] -> {
      let #(parsed_id, new_pos, new_span) = case rest {
        [] -> #(0, pos + 1, span)
        [Token("Integer", v, s), .._] -> {
          let id = case int.parse(v) { Ok(n) -> n Error(_) -> 0 }
          let loc_span = Span(s.file, s.start_line, s.start_col, s.end_line, s.end_col)
          #(id, pos + 2, loc_span)
        }
        _ -> #(0, pos + 1, span)
      }
      #(Hole(parsed_id, new_span), #(tokens, new_pos, env, fn_, errors))
    }
    
    // Prefixed tokens: % followed by keyword (lexer produces separate tokens)
    [Token("Op", "%", _), Token("Name", "fn", _), ..rest] ->
      parse_lambda(#(rest, 0, env, fn_, errors), span)
    [Token("Op", "%", _), Token("Name", "let", _), ..rest] ->
      parse_let(#(rest, 0, env, fn_, errors), span)
    [Token("Op", "%", _), Token("Name", "match", _), ..rest] ->
      parse_match(#(rest, 0, env, fn_, errors), span)
    [Token("Op", "%", _), Token("Name", "fix", _), ..rest] ->
      parse_fix(#(rest, 0, env, fn_, errors), span)
    // Keywords and prefixed tokens
    [Token("Name", v, _), .._] -> {
      case v {
        "%" -> parse_hole(#(tokens, pos + 1, env, fn_, errors), span)
        "hole" -> #(Hole(0, span), #(tokens, pos + 1, env, fn_, errors))
        "unit" -> #(Rcd([], span), #(tokens, pos + 1, env, fn_, errors))
        "type" -> #(Typ(0, span), #(tokens, pos + 1, env, fn_, errors))
        "true" -> #(Rcd([], span), #(tokens, pos + 1, env, fn_, errors))
        "fun" -> parse_app(#(tokens, pos + 1, env, fn_, errors), span)
        _ -> parse_var(#(tokens, pos + 1, env, fn_, errors), v, span)
      }
    }
    
    // Operators
    [Token("Op", v, _), .._] -> {
      case v {
        "-" -> {
          let p = #(tokens, pos + 1, env, fn_, errors)
          let #(body, p2) = parse_term(p)
          let app_span = merge(span, term_span(body))
          let e = Err("negation not supported: " <> term_to_string(body), app_span)
          #(e, p2)
        }
        "!" -> {
          let p = #(tokens, pos + 1, env, fn_, errors)
          let #(body, p2) = parse_term(p)
          let app_span = merge(span, term_span(body))
          let e = Err("not not supported: " <> term_to_string(body), app_span)
          #(e, p2)
        }
        _ -> {
          let e = Err("unexpected operator: " <> v, span)
          #(e, #(tokens, pos + 1, env, fn_, errors))
        }
      }
    }
    
    // Parenthesized expressions: (expr) or (term : Type)
    [Token("Punct", "(", _), ..rest] -> {
      let p = #(rest, 0, env, fn_, errors)
      let #(inner, p2) = parse_term(p)
      let p3 = skip(")", p2)
      #(inner, p3)
    }
    
    // Punctuation
    [Token("Punct", "[", _), ..rest] -> parse_list(#(rest, 0, env, fn_, errors), span)
    [Token("Punct", "{", _), ..rest] -> parse_rcd(#(rest, 0, env, fn_, errors), span)
    [Token("Punct", "(", _), Token("Punct", ")", _), ..rest] -> #(Rcd([], span), #(rest, 2, env, fn_, errors))
    [Token("Punct", "#", _), ..rest] -> parse_ctr(#(rest, 0, env, fn_, errors), span)
    [Token("Eof", ..), ..] -> { let e = Err("unexpected end of input", span)#(e, p) }
    [Token(_, v, _), .._] -> {
      let e = Err("unexpected token: " <> v, span)
      #(e, #(tokens, pos + 1, env, fn_, errors))
    }
  }
}

// Hole: %name
fn parse_hole(p: Parser, span: Span) -> #(Term, Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [Token("Name", name, _), ..] -> {
      let parsed = case int.parse(name) {
        Ok(n) -> n
        Error(_) -> 0
      }
      #(Hole(parsed, span), #(tokens, pos + 1, env, fn_, errors))
    }
    _ -> {
      let e = Err("expected hole name after %", span)
      #(e, p)
    }
  }
}

// Type: %Type or %Type(n)
// Constructor: #Tag or #Tag(arg)
fn parse_ctr(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("#", p)
  let #(name, p2) = expect_name_opt(p1)
  case name {
    "" -> {
      let e = Err("expected constructor name after #", span)
      #(e, p1)
    }
    _ -> {
      let arg_span = current_span(p2)
      let #(tokens, pos, env, fn_, errors) = p2
      case list.drop(tokens, pos) {
        [Token("Punct", "(", _), ..rest] -> {
          let p3 = #(rest, 0, env, fn_, errors)
          let #(arg, p4) = parse_term(p3)
          let p5 = skip(")", p4)
          let rcd = Rcd([#("arg", arg)], arg_span)
          #(Ctr(name, rcd, span), p5)
        }
        _ -> {
          let rcd = Rcd([], span)
          #(Ctr(name, rcd, span), p2)
        }
      }
    }
  }
}

// Record: {x: 1, y: 2}
fn parse_rcd(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("{", p)
  let #(fields, p2) = parse_rcd_fields(p1, [])
  let p3 = skip("}", p2)
  #(Rcd(fields, span), p3)
}

fn parse_rcd_fields(p: Parser, acc: List(#(String, Term))) -> #(List(#(String, Term)), Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> { let err = ParseError(span: current_span(p), expected: "field", got: "EOF", context: "in record")#(list.reverse(acc), #(tokens, pos, env, fn_, [err, ..errors])) }
    [Token("Punct", "}", _), ..rest] -> #(list.reverse(acc), #(rest, pos + 1, env, fn_, errors))
    [Token("Eof", ..), ..] -> #(list.reverse(acc), p)
    _ -> {
      let p1 = skip("Name", p)
      let #(name, p2) = expect_name_opt(p1)
      let p3 = skip(":", p2)
      let #(value, p4) = parse_term(p3)
      let p5 = skip(",", p4)
      parse_rcd_fields(p5, [ #(name, value), ..acc ])
    }
  }
}

fn parse_var(p: Parser, name: String, span: Span) -> #(Term, Parser) {
  case is_keyword(name) {
    True -> { let e = Err("unexpected keyword: " <> name, span)#(e, p) }
    False -> {
      let #(tokens, pos, env, fn_, errors) = p
      let depth = list.length(env)
      case lookup_var(env, name, depth) {
        Ok(index) -> #(Var(index, span), p)
        Error(_) -> {
          let err = ParseError(span: span, expected: "variable '" <> name <> "'", got: "undefined", context: "variable not found")
          #(Err("undefined variable: " <> name, span), #(tokens, pos, env, fn_, [err, ..errors]))
        }
      }
    }
  }
}

fn lookup_var(env: List(#(String, Int)), name: String, depth: Int) -> Result(Int, Nil) {
  lookup_loop(env, name, 0, depth)
}

fn lookup_loop(env: List(#(String, Int)), name: String, idx: Int, depth: Int) -> Result(Int, Nil) {
  case env {
    [] -> Error(Nil)
    [#(n, d), ..rest] -> {
      case n == name {
        True -> Ok(depth - d)
        False -> lookup_loop(rest, name, idx + 1, depth)
      }
    }
  }
}

// Lambda: %fn(name: Type) => body
fn parse_lambda(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("(", p)
  let #(name, p2) = expect_name_opt(p1)
  let p3 = skip(":", p2)
  let #(param_type, p4) = parse_term(p3)
  let p5 = skip(")", p4)
  let p6 = skip("=>", p5)
  let p7 = add_binding(p6, name)
  let #(body, rest) = parse_term(p7)
  let final_span = merge(span, term_span(body))
  #(Lam(#(name, param_type, body), body, final_span), rest)
}

// Application: fun(fun_arg: arg)
fn parse_app(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("(", p)
  let p2 = skip(":", p1)
  let #(fun_arg, rest1) = parse_term(p2)
  let p3 = skip(")", rest1)
  let p4 = skip(",", p3)
  let #(arg, rest_errors) = parse_term(p4)
  let final_span = merge(span, term_span(arg))
  #(App(fun_arg, arg, final_span), rest_errors)
}

// Match: %match arg { | pattern ? guard => body }
fn parse_match(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("%", p)
  let p2 = skip("match", p1)
  let p3 = skip("arg", p2)
  let #(arg, p4) = parse_term(p3)
  let p5 = skip("{", p4)
  let p6 = parse_cases(p5)
  let #(cases, rest) = p6
  let p7 = skip("}", rest)
  let final_span = merge(span, case_list_span(cases, span))
  #(Match(arg, cases, final_span), p7)
}

fn parse_cases(p: Parser) -> #(List(Case), Parser) {
  let #(cases, p1) = parse_cases_acc(p, [])
  #(list.reverse(cases), p1)
}

fn parse_cases_acc(p: Parser, acc: List(Case)) -> #(List(Case), Parser) {
  let span = current_span(p)
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> { let err = ParseError(span: current_span(p), expected: "case pattern", got: "EOF", context: "end of match")#(acc, #(tokens, pos, env, fn_, [err, ..errors])) }
    [Token("Punct", "}", _), ..rest] -> #(acc, #(rest, pos + 1, env, fn_, errors))
    [Token("Eof", ..), ..] -> #(acc, p)
    _ -> {
      let p1 = skip("|", p)
      let #(pattern, _) = parse_pattern(p1)
      let #(guard, p3) = case list.drop(tokens, pos) {
        [Token("Op", "?", _), ..] -> {
          let p = #(tokens, pos + 1, env, fn_, errors)
          let #(g, p2) = parse_term(p)
          #(Some(g), p2)
        }
        _ -> #(None, p)
      }
      let p4 = skip("=>", p3)
      let #(body, rest_errors) = parse_term(p4)
      let case_term = CoreCase(pattern, guard, body, span)
      parse_cases_acc(rest_errors, [case_term, ..acc])
    }
  }
}

// Let: %let name = value; body — desugars to App(Lam(name, _, body), value)
fn parse_let(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("let", p)
  let #(name, p2) = expect_name_opt(p1)
  let p3 = skip("=", p2)
  let #(value, rest) = parse_term(p3)
  let p4 = skip(";", rest)
  let let_span = merge(span, term_span(value))
  let #(body, rest_final) = parse_term(p4)
  let body_span = merge(let_span, term_span(body))
  let param_type = Rcd([], span)
  #(let_var(name, param_type, value, body, body_span), rest_final)
}

// Fix: %fix name = body — desugars to App(Lam(name, _, body), value)
fn parse_fix(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("fix", p)
  let #(name, p2) = expect_name_opt(p1)
  let p3 = skip("=", p2)
  let #(body, rest_errors) = parse_term(p3)
  let final_span = merge(span, term_span(body))
  let param_type = Rcd([], span)
  #(let_var(name, param_type, body, body, final_span), rest_errors)
}

// If: if cond then body else else_body
// List: [1, 2, 3]
fn parse_list(p: Parser, span: Span) -> #(Term, Parser) {
  let #(items, p1) = parse_list_items(p)
  let p2 = skip("]", p1)
  let fields = list.index_map(items, fn(item, i) { #(int.to_string(i), item) })
  let result = Rcd(fields, span)
  #(result, p2)
}

fn parse_list_items(p: Parser) -> #(List(Term), Parser) {
  parse_list_items_acc(p, [])
}

fn parse_list_items_acc(p: Parser, acc: List(Term)) -> #(List(Term), Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> { let err = ParseError(span: current_span(p), expected: "list item", got: "EOF", context: "in list")#(list.reverse(acc), #(tokens, pos, env, fn_, [err, ..errors])) }
    [Token("Punct", "]", _), ..rest] -> #(list.reverse(acc), #(rest, pos + 1, env, fn_, errors))
    [Token("Eof", ..), ..] -> #(list.reverse(acc), p)
    _ -> {
      let #(item, p1) = parse_term(p)
      let p2 = skip(",", p1)
      parse_list_items_acc(p2, [item, ..acc])
    }
  }
}

// Pattern: _, name, name(arg), (), 42
fn parse_pattern(p: Parser) -> #(Pattern, Parser) {
  let span = current_span(p)
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> #(PAny(span), p)
    [Token("_", _, _), .._] -> #(PAny(span), #(tokens, pos + 1, env, fn_, errors))
    [Token("Name", v, _), ..rest] -> {
      let p1 = #(tokens, pos + 1, env, fn_, errors)
      case rest {
        [] -> #(PVar(v, span), p1)
        [Token("Punct", "(", _), ..inner_rest] -> {
          let p2 = #(inner_rest, 0, env, fn_, errors)
          let #(inner, p3) = parse_pattern(p2)
          let p4 = skip(")", p3)
          let final_span = merge(span, current_span(p4))
          #(PCtr(v, inner, final_span), p4)
        }
        _ -> #(PVar(v, span), p1)
      }
    }
    [Token("Punct", "(", _), Token("Punct", ")", _), ..rest] -> {
      let p1 = #(tokens, pos + 2, env, fn_, errors)
      #(PUnit(span), p1)
    }
    [Token("Integer", v, _), .._] -> {
      let p1 = #(tokens, pos + 1, env, fn_, errors)
      case int.parse(v) {
        Ok(value) -> #(PLit(LitInt(value), span), p1)
        Error(_) -> { let err = ParseError(span: span, expected: "integer", got: v, context: "invalid integer literal")#(PAny(span), #(tokens, pos + 1, env, fn_, [err, ..errors])) }
      }
    }
    [Token("Float", v, _), .._] -> {
      let p1 = #(tokens, pos + 1, env, fn_, errors)
      case float.parse(v) {
        Ok(value) -> #(PLit(LitFloat(value), span), p1)
        Error(_) -> { let err = ParseError(span: span, expected: "float", got: v, context: "invalid float literal")#(PAny(span), #(tokens, pos + 1, env, fn_, [err, ..errors])) }
      }
    }
    _ -> #(PAny(span), p)
  }
}

fn case_list_span(cases: List(Case), default: Span) -> Span {
  case cases {
    [] -> default
    [first, ..rest] -> {
      case list.last(rest) {
        Ok(last) -> merge(first.span, last.span)
        Error(_) -> first.span
      }
    }
  }
}

fn term_to_string(term: Term) -> String {
  case term {
    Var(_, _) -> "var"
    Hole(_, _) -> "hole"
    Lam(_, _, _) -> "fn"
    App(_, _, _) -> "app"
    Pi(_, _, _) -> "Pi"
    Lit(_, _) -> "lit"
    Ctr(_, _, _) -> "ctr"
    Match(_, _, _) -> "match"
    Ann(_, _, _) -> "ann"
    Rcd(_, _) -> "rcd"
    Typ(_, _) -> "type"
    Err(msg, _) -> msg
  }
}

fn is_keyword(s: String) -> Bool {
  case s {
    "fn" | "let" | "in" | "match" | "case" | "type" | "of"
    | "fun" | "fix" | "hole" | "unit" | "true" | "false"
    | "if" | "then" | "else" | "import" | "as" -> True
    _ -> False
  }
}
