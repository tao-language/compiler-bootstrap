/// Core Language Parser
///
/// Parses source strings into Core AST terms with De Bruijn indices.

import core/ast.{type Term, type Pattern, type Case,
  Var, Hole, Lam, App, Pi, Lit, Ctr, Match, Let, Ann, Unit, Typ, Err,
  Case as CoreCase, PAny, PVar, PCtr, PUnit, PLit, Int as LitInt, Float as LitFloat}
import syntax/base_lexer.{Token, type Token, tokenize}
import syntax/grammar.{type ParseError, ParseError}
import syntax/span.{type Span, single, merge}
import gleam/list
import gleam/int
import gleam/float

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

fn add_binding(p: Parser, name: String, depth: Int) -> Parser {
  let #(tokens, pos, env, fn_, errors) = p
  #(tokens, pos, [ #(name, depth), ..env ], fn_, errors)
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
    Let(_, _, _, span) -> span
    Ann(_, _, span) -> span
    Unit(span) -> span
    Typ(span) -> span
    Err(_, span) -> span
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

fn skip(kind: String, p: Parser) -> Parser {
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [Token(k, _, _), .._] if k == kind -> #(tokens, pos + 1, env, fn_, errors)
    _ -> p
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
    [Token("String", v, _), .._] -> {
      let e = Err("string literal not supported: " <> v, span)
      #(e, #(tokens, pos + 1, env, fn_, errors))
    }
    [Token("Name", v, _), .._] -> {
      case v {
        "fn" -> parse_lambda(#(tokens, pos + 1, env, fn_, errors), span)
        "let" -> parse_let(#(tokens, pos + 1, env, fn_, errors), span)
        "match" -> parse_match(#(tokens, pos + 1, env, fn_, errors), span)
        "fix" -> parse_fix(#(tokens, pos + 1, env, fn_, errors), span)
        "hole" -> #(Hole(0, span), #(tokens, pos + 1, env, fn_, errors))
        "unit" -> #(Unit(span), #(tokens, pos + 1, env, fn_, errors))
        "type" -> #(Typ(span), #(tokens, pos + 1, env, fn_, errors))
        "true" -> #(Unit(span), #(tokens, pos + 1, env, fn_, errors))
        "fun" -> parse_pi(#(tokens, pos + 1, env, fn_, errors), span)
        "if" -> parse_if(#(tokens, pos + 1, env, fn_, errors), span)
        _ -> parse_var(#(tokens, pos + 1, env, fn_, errors), v, span)
      }
    }
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
    [Token("Punct", "(", _), ..rest] -> {
      let p = #(rest, 1, env, fn_, errors)
      let #(inner, p2) = parse_term(p)
      let p3 = skip(")", p2)
      #(inner, p3)
    }
    [Token("Punct", "[", _), ..rest] -> parse_list(#(rest, 1, env, fn_, errors), span)
    [Token("Eof", ..), ..] -> { let e = Err("unexpected end of input", span)#(e, p) }
    [Token(_, v, _), .._] -> {
      let e = Err("unexpected token: " <> v, span)
      #(e, #(tokens, pos + 1, env, fn_, errors))
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

fn parse_lambda(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("(", p)
  let #(name, p2) = expect_name_opt(p1)
  let p3 = skip(")", p2)
  let p4 = skip("->", p3)
  let p5 = add_binding(p4, name, 0)
  let #(body, rest) = parse_term(p5)
  let final_span = merge(span, term_span(body))
  #(Lam(#(name, body), body, final_span), rest)
}

fn parse_pi(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("(", p)
  let p2 = case expect_name_opt(p1) {
    #("", p) -> p
    #(_, p) -> p
  }
  let p3 = skip(":", p2)
  let #(domain, rest1) = parse_term(p3)
  let p4 = skip(")", rest1)
  let p5 = skip("->", p4)
  let #(codomain, rest_errors) = parse_term(p5)
  let final_span = merge(span, term_span(codomain))
  #(Pi(domain, codomain, final_span), rest_errors)
}

fn parse_match(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("{", p)
  let #(arg, rest1) = parse_term(p1)
  let #(cases, rest2) = parse_cases(rest1)
  let p3 = skip("}", rest2)
  let final_span = merge(span, case_list_span(cases, span))
  #(Match(arg, cases, final_span), p3)
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
      let #(pattern, p1) = parse_pattern(p)
      let p2 = skip("=>", p1)
      let #(body, rest_errors) = parse_term(p2)
      let case_term = CoreCase(pattern, body, span)
      parse_cases_acc(rest_errors, [case_term, ..acc])
    }
  }
}

fn parse_let(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("=", p)
  let #(name, p2) = expect_name_opt(p1)
  let #(value, rest_errors) = parse_term(p2)
  let let_span = merge(span, term_span(value))
  #(Let(name, value, Unit(let_span), let_span), rest_errors)
}

fn parse_fix(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("fix", p)
  let #(name, p2) = expect_name_opt(p1)
  let #(body, rest_errors) = parse_term(p2)
  let final_span = merge(span, term_span(body))
  #(Let(name, body, Unit(final_span), final_span), rest_errors)
}

fn parse_if(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("then", p)
  let #(cond, rest1) = parse_term(p1)
  let p2 = skip("else", rest1)
  let #(then_body, rest2) = parse_term(p2)
  let #(else_body, rest3) = parse_term(rest2)
  let cases = [
    CoreCase(PUnit(span), else_body, span),
    CoreCase(PAny(span), then_body, span),
  ]
  let final_span = merge(span, term_span(else_body))
  #(Match(cond, cases, final_span), rest3)
}

fn parse_list(p: Parser, span: Span) -> #(Term, Parser) {
  let #(items, p1) = parse_list_items(p)
  let p2 = skip("]", p1)
  let result = list.fold(items, Ctr("#", Unit(span), span), fn(_acc: Term, item: Term) { Ctr("#", item, span) })
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
          let p2 = #(inner_rest, 1, env, fn_, errors)
          let #(inner, p3) = parse_pattern(p2)
          let p4 = skip(")", p3)
          let final_span = merge(span, current_span(p4))
          #(PCtr(v, inner, final_span), p4)
        }
        _ -> #(PVar(v, span), p1)
      }
    }
    [Token("Punct", "()", _), .._] -> {
      let p1 = #(tokens, pos + 1, env, fn_, errors)
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
    Let(_, _, _, _) -> "let"
    Ann(_, _, _) -> "ann"
    Unit(_) -> "unit"
    Typ(_) -> "type"
    Err(msg, _) -> msg
  }
}
