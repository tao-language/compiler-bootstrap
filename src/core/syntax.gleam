/// Core Language Parser
///
/// Parses source strings into Core AST terms with De Bruijn indices.
///
/// Syntax:
///   - Variables: x, y, z
///   - Holes: ? or ?0, ?1
///   - Lambda: $fn(name: Type) => body
///   - Lambda (untyped): $fn(name) => body
///   - Lambda (implicit): $fn<a: Type>(x: Type) => body
///   - Application: fun(fun_arg: arg)
///   - Pi type: $pi(name: Domain) -> Codomain
///   - Pi type (implicit): $pi<a: Type>(a) -> a
///   - Pi type (untyped): $pi(name) -> type
///   - Literals: 42, 3.14
///   - Constructors: #Tag, #Tag(arg)
///   - Match: $match arg { | pattern => body }
///   - Match (guard): $match arg { | pattern ? guard ~ pass => body }
///   - Let: $let name = value; body
///   - Let (untyped): $let name = value; body
///   - Annotation: (term : Type)
///   - Unit: () or {}
///   - Type: $Type, $Type(1), $Type<x>
///   - Errors: $error "message"
///   - Records: {x: 1, y: 2}
///   - FFI calls: $fn(arg: Type, arg: Type) -> ReturnType
///   - Type definitions: $type { | #C(arg) -> ResultType }
import core/ast.{
  type Case, type Pattern, type Term, Ann, App, Call, Case as CoreCase, Ctr, Err, TypeDef,
  Float as LitFloat, Hole, Int as LitInt, Lam, Lit, Match, PAny, PAlias, PCtr, PError, PLit,
  PType, PRcd, PUnit, PVar, Pi, Rcd, Typ, Var, let_var,
}
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{None, Some}
import syntax/base_lexer.{type Token, Token, tokenize}
import syntax/grammar.{type ParseError, ParseError}
import syntax/span.{type Span, Span, merge, single}

/// Parse a Core source string into a Term.
pub fn parse(source: String) -> #(Term, List(ParseError)) {
  let tokens = tokenize(source)
  parse_tokens(tokens, "")
}

/// Parse tokens into a Core term.
pub fn parse_tokens(
  tokens: List(Token),
  filename: String,
) -> #(Term, List(ParseError)) {
  let state = #(tokens, 0, [], filename, [])
  let span = single(filename, 1, 1)
  let #(term, state2) = parse_term_with_app(state, span)
  let #(tokens2, pos2, _, _, errs) = state2
  case term {
    Err(msg, _) -> #(Err(msg, span), errs)
    t -> {
      let rest = try_peek(tokens2, pos2)
      case rest {
        Error(_) -> #(t, errs)
        Ok(Token(kind: "Eof", value: "", span: _)) -> #(t, errs)
        Ok(Token(kind: _, value: value, span: span)) -> {
          let err =
            ParseError(
              span: span,
              expected: "end of input",
              got: value,
              context: "unexpected token",
            )
          #(t, [err, ..errs])
        }
      }
    }
  }
}

type Parser =
  #(List(Token), Int, List(#(String, Int)), String, List(ParseError))

fn try_peek(tokens: List(Token), pos: Int) -> Result(Token, List(ParseError)) {
  case list.drop(tokens, pos) {
    [] -> Error([])
    [t, ..] -> Ok(t)
  }
}

fn add_binding(p: Parser, name: String) -> Parser {
  let #(tokens, pos, env, fn_, errors) = p
  let new_depth = list.length(env) + 1
  #(tokens, pos, [#(name, new_depth), ..env], fn_, errors)
}

fn current_span(p: Parser) -> Span {
  let #(tokens, pos, _, fn_, _) = p
  case list.drop(tokens, pos) {
    [] -> single(fn_, 1, 1)
    [Token(_, _, span), ..] -> span
  }
}

/// Get span for a specific position in the token stream.
fn span_for_pos(tokens: List(Token), pos: Int) -> Span {
  case list.drop(tokens, pos) {
    [] -> single("unknown", 0, 0)
    [Token(_, _, span), ..] -> span
  }
}

fn term_span(term: Term) -> Span {
  case term {
    Var(_, span) -> span
    Hole(_, span) -> span
    Lam(_, _, _, span) -> span
    App(_, _, span) -> span
    Pi(_, _, _, span) -> span
    Lit(_, span) -> span
    Ctr(_, _, span) -> span
    Match(_, _, span) -> span
    Ann(_, _, span) -> span
    Call(_, _, _, _, span) -> span
    Rcd(_, span) -> span
    Typ(_, span) -> span
    TypeDef(_, _, span) -> span
    Err(_, span) -> span
  }
}

fn skip(kind: String, p: Parser) -> Parser {
  let #(tokens, pos, env, fn_, errors) = p
  case kind {
    "->" -> {
      case list.drop(tokens, pos) {
        [Token("Op", "-", _), Token("Op", ">", _), ..] -> #(
          tokens,
          pos + 2,
          env,
          fn_,
          errors,
        )
        _ -> {
          let got = case list.drop(tokens, pos) {
            [Token(k, v, _), ..] -> k <> " '" <> v <> "'"
            [] -> "end of input"
            _ -> "unexpected token"
          }
          let err = ParseError(
            span: span_for_pos(tokens, pos),
            expected: "->",
            got: got,
            context: "",
          )
          #(tokens, pos, env, fn_, [err, ..errors])
        }
      }
    }
    "=>" -> {
      case list.drop(tokens, pos) {
        [Token("Punct", "=", _), Token("Op", ">", _), ..] -> #(
          tokens,
          pos + 2,
          env,
          fn_,
          errors,
        )
        _ -> {
          let got = case list.drop(tokens, pos) {
            [Token(k, v, _), ..] -> k <> " '" <> v <> "'"
            [] -> "end of input"
            _ -> "unexpected token"
          }
          let err = ParseError(
            span: span_for_pos(tokens, pos),
            expected: "=>",
            got: got,
            context: "",
          )
          #(tokens, pos, env, fn_, [err, ..errors])
        }
      }
    }
    _ -> {
      case list.drop(tokens, pos) {
        [Token(k, _, _), ..] if k == kind -> #(
          tokens,
          pos + 1,
          env,
          fn_,
          errors,
        )
        [Token("Punct", pval, _), ..] if pval == kind -> #(
          tokens,
          pos + 1,
          env,
          fn_,
          errors,
        )
        [Token("Op", opval, _), ..] if opval == kind -> #(
          tokens,
          pos + 1,
          env,
          fn_,
          errors,
        )
        [Token("Name", nval, _), ..] if nval == kind -> #(
          tokens,
          pos + 1,
          env,
          fn_,
          errors,
        )
        _ -> p
      }
    }
  }
}

fn expect_name_opt(p: Parser) -> #(String, Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [Token("Name", v, _), ..] -> #(v, #(tokens, pos + 1, env, fn_, errors))
    _ -> #("", p)
  }
}

fn parse_term(p: Parser) -> #(Term, Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  let span = current_span(p)
  case list.drop(tokens, pos) {
    [] -> {
      let e = Err("unexpected end of input", span)
      #(e, p)
    }

    // Integer and float literals
    [Token("Integer", v, _), ..] ->
      case int.parse(v) {
        Ok(value) -> #(
          Lit(LitInt(value), span),
          #(tokens, pos + 1, env, fn_, errors),
        )
        Error(_) -> {
          let e = Err("invalid integer: " <> v, span)
          #(e, #(tokens, pos + 1, env, fn_, errors))
        }
      }
    [Token("Float", v, _), ..] ->
      case float.parse(v) {
        Ok(value) -> #(
          Lit(LitFloat(value), span),
          #(tokens, pos + 1, env, fn_, errors),
        )
        Error(_) -> {
          let e = Err("invalid float: " <> v, span)
          #(e, #(tokens, pos + 1, env, fn_, errors))
        }
      }

    // String literals - error
    [Token("String", v, _), ..] -> {
      let e = Err("string literal not supported: " <> v, span)
      #(e, #(tokens, pos + 1, env, fn_, errors))
    }

    // Holes: ? or ?0, ?1
    [Token("Op", "?", _), ..rest] -> {
      let #(parsed_id, new_pos, new_span) = case rest {
        [] -> #(0, pos + 1, span)
        [Token("Integer", v, s), ..] -> {
          let id = case int.parse(v) {
            Ok(n) -> n
            Error(_) -> 0
          }
          let loc_span =
            Span(s.file, s.start_line, s.start_col, s.end_line, s.end_col)
          #(id, pos + 2, loc_span)
        }
        _ -> #(0, pos + 1, span)
      }
      #(Hole(parsed_id, new_span), #(tokens, new_pos, env, fn_, errors))
    }

    // Record type syntax: ${field: type, ...} (parsed as record term)
    [Token("Op", "$", _), Token("Punct", "{", _), ..rest] -> {
      let p1 = #(rest, 0, env, fn_, errors)
      let #(fields, p2) = parse_rcd_fields(p1, [])
      let p3 = skip("}", p2)
      #(Rcd(fields, span), p3)
    }
    // Prefixed tokens: $ followed by keyword
    [Token("Op", "$", _), Token("Name", "fn", _), ..rest] ->
      parse_lambda(#(rest, 0, env, fn_, errors), span)
    [Token("Op", "$", _), Token("Name", "let", _), ..rest] ->
      parse_let(#(rest, 0, env, fn_, errors), span)
    [Token("Op", "$", _), Token("Name", "match", _), ..rest] ->
      parse_match(#(tokens, pos, env, fn_, errors), span)
    // Also support plain match (without $)
    [Token("Name", "match", _), ..rest] ->
      parse_match(#(tokens, pos, env, fn_, errors), span)
    [Token("Op", "$", _), Token("Name", "fix", _), ..rest] ->
      parse_fix(#(rest, 0, env, fn_, errors), span)
    // Type definition: $type { | #C(args) -> ReturnType } or $type<>(...)
    [Token("Op", "$", _), Token("Name", "type", _), ..rest] ->
      parse_type_def(#(rest, 0, env, fn_, errors), span)
    // Error term: $error "message" or $error (without message)
    [Token("Op", "$", _), Token("Name", "error", _), Token("String", msg, _), ..rest] ->
      #(Err(msg, span), #(rest, 0, env, fn_, errors))
    [Token("Op", "$", _), Token("Name", "error", _), ..rest] ->
      #(Err("error", span), #(rest, 0, env, fn_, errors))
    // Numeric type keywords as first-class values: $Int, $Float, $I8-$I64, $U8-$U64, $F16-$F64
    [Token("Op", "$", _), Token("Name", name, _), ..rest] ->
      #(Ctr(name, Hole(0, span), span), #(rest, 0, env, fn_, errors))
    // FFI builtin calls: % followed by function name
    [Token("Op", "%", _), Token("Name", v, _), ..rest] ->
      parse_ffi_call(#(rest, 0, env, fn_, errors), v, span)
    // Keywords and prefixed tokens
    [Token("Name", v, _), ..] -> {
      case v {
        "hole" -> #(Hole(0, span), #(tokens, pos + 1, env, fn_, errors))
        "unit" -> #(Rcd([], span), #(tokens, pos + 1, env, fn_, errors))
        "type" -> #(Typ(0, span), #(tokens, pos + 1, env, fn_, errors))
        "true" -> #(Rcd([], span), #(tokens, pos + 1, env, fn_, errors))
        "fun" -> parse_app(#(tokens, pos + 1, env, fn_, errors), span)
        _ -> {
          let #(var_term, var_rest) = parse_var(#(tokens, pos + 1, env, fn_, errors), v, span)
          parse_app_chain(var_rest, var_term, span)
        }
      }
    }

    // Operators
    [Token("Op", v, _), ..] -> {
      case v {
        "#" -> {
          let #(tokens, pos, env, fn_, errors) = p
          let span = current_span(p)
          parse_ctr(#(tokens, pos + 1, env, fn_, errors), span)
        }
        "-" -> {
          let p = #(tokens, pos + 1, env, fn_, errors)
          let #(body, p2) = parse_term(p)
          let app_span = merge(span, term_span(body))
          let e =
            Err("negation not supported: " <> term_to_string(body), app_span)
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
    // Also handles () as unit (Rcd with empty fields)
    [Token("Punct", "(", _), Token("Punct", ")", _), ..rest] -> #(
      Rcd([], span),
      #(rest, 2, env, fn_, errors),
    )
    [Token("Punct", "(", _), ..rest] -> {
      let p = #(rest, 0, env, fn_, errors)
      let #(inner, p2) = parse_term(p)
      let p3 = skip(")", p2)
      #(inner, p3)
    }

    // Punctuation
    [Token("Punct", "[", _), ..rest] ->
      parse_list(#(rest, 0, env, fn_, errors), span)
    [Token("Punct", "{", _), ..rest] ->
      parse_rcd(#(rest, 0, env, fn_, errors), span)
    [Token(_, "#", _), ..rest] ->
      parse_ctr(#(rest, 0, env, fn_, errors), span)
    [Token("Eof", ..), ..] -> {
      let e = Err("unexpected end of input", span)
      #(e, p)
    }
    [Token(_, v, _), ..] -> {
      let e = Err("unexpected token: " <> v, span)
      #(e, #(tokens, pos + 1, env, fn_, errors))
    }
  }
}

/// Parse a term optionally followed by application arguments.
/// E.g., `fun(arg)` or `(fun)(arg)` are parsed as App(fun, arg).
fn parse_term_with_app(p: Parser, span: Span) -> #(Term, Parser) {
  let #(term, rest) = parse_term(p)
  parse_app_chain(rest, term, span)
}

/// Recursively parse application arguments.
fn parse_app_chain(p: Parser, fun: Term, span: Span) -> #(Term, Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [Token("Punct", "(", _), ..rest] -> {
      let p_arg = #(rest, 0, env, fn_, errors)
      let #(arg, p2) = parse_term(p_arg)
      let p3 = skip(")", p2)
      let app_span = merge(span, term_span(arg))
      let app = App(fun, arg, app_span)
      parse_app_chain(p3, app, app_span)
    }
    [Token("Op", "~", _), ..rest] -> {
      let p_rhs = #(rest, 0, env, fn_, errors)
      let #(rhs, p2) = parse_pattern(p_rhs)
      let match_span = merge(span, term_span(fun))
      // Encode `fun ~ rhs` as `$match fun { | rhs => #True | _ => #False }`
      let match_term = Match(
        fun,
        [
          CoreCase(rhs, None, Ctr("True", Rcd([], match_span), match_span), match_span),
          CoreCase(PAny(match_span), None, Ctr("False", Rcd([], match_span), match_span), match_span),
        ],
        match_span,
      )
      parse_app_chain(p2, match_term, match_span)
    }
    _ -> #(fun, p)
  }
}

// FFI call: %name(arg: Type, arg: Type) -> ReturnType
fn parse_ffi_call(p: Parser, name: String, _span: Span) -> #(Term, Parser) {
  let p1 = skip("(", p)
  let #(typed_args, p2) = parse_typed_arg_list(p1)
  let p3 = skip(")", p2)
  let #(rtokens, rpos, renv, rfn_, rerrors) = p3
  let _p4 = #(rtokens, rpos, renv, rfn_, rerrors)
  let #(return_type, p5) = case list.drop(rtokens, rpos) {
    [Token("Op", "->", _), ..] -> {
      let p6 = #(rtokens, rpos + 1, renv, rfn_, rerrors)
      let #(rt, p7) = parse_term(p6)
      #(Some(rt), p7)
    }
    _ -> #(None, p3)
  }
  let final_span = current_span(p5)
  let arg_list = list.map(typed_args, fn(t) { t.0 })
  #(Call(name, arg_list, typed_args, return_type, final_span), p5)
}

// Parse a comma-separated list of typed arguments (arg: Type, arg: Type)
fn parse_typed_arg_list(p: Parser) -> #(List(#(Term, Term)), Parser) {
  parse_typed_arg_list_acc(p, [])
}

fn parse_typed_arg_list_acc(p: Parser, acc: List(#(Term, Term))) -> #(List(#(Term, Term)), Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  let p1 = #(tokens, pos, env, fn_, errors)
  let p2 = skip(",", p1)
  let #(tokens2, pos2, _env2, _fn2, _errors2) = p2
  case list.drop(tokens2, pos2) {
    [Token("Punct", ")", _), ..] -> #(list.reverse(acc), p2)
    _ -> {
      let #(arg, p4) = parse_term(p2)
      // Guard: if parse_term didn't advance, we're not at a valid argument.
      // Return accumulated args to avoid infinite loop.
      case p4 {
        #(tokens4, pos4, env4, fn4, errors4) ->
          case pos4 == pos2 {
            True -> #(list.reverse(acc), p4)
            False -> {
              let p5 = #(tokens4, pos4, env4, fn4, errors4)
              let p6 = skip(":", p5)
              let #(ttokens, tpos, tenv, tfn_, terrors) = p6
              let p7 = #(ttokens, tpos, tenv, tfn_, terrors)
              let #(type_, p8) = parse_term(p7)
              parse_typed_arg_list_acc(p8, [#(arg, type_), ..acc])
            }
          }
      }
    }
  }
}

// Type definition: $type { | #C(args) -> ReturnType } or $type<>(...)
fn parse_type_def(p: Parser, span: Span) -> #(Term, Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    // $type<> -> type with explicit empty type params, then { ... }
    [Token("Op", "<", _), Token("Op", ">", _), ..rest] -> {
      let p1 = #(rest, 0, env, fn_, errors)
      let #(rtokens, rpos, renv, rfn_, rerrors) = p1
      case list.drop(rtokens, rpos) {
        [Token("Punct", "{", _), ..rest2] -> {
          let p2 = #(rest2, rpos + 1, renv, rfn_, rerrors)
          let #(body, p3) = parse_type_def_body(p2)
          let #(ttokens, tpos, tenv, tfn_, terrors) = p3
          let p4 = #(ttokens, tpos, tenv, tfn_, terrors)
          #(TypeDef("", body, current_span(p4)), p4)
        }
        _ -> #(Typ(0, span), p1)
      }
    }
    // $type { ... }
    [Token("Punct", "{", _), ..rest] -> {
      let p1 = #(rest, 0, env, fn_, errors)
      let #(body, p2) = parse_type_def_body(p1)
      let p3 = skip("}", p2)
      let #(tokens, pos, env, fn_, errors) = p3
      #(TypeDef("", body, current_span(p3)), p3)
    }
    // $type alone -> universe type
    _ -> #(Typ(0, span), p)
  }
}

// Parse type definition body: { | #C(arg) -> ReturnType }
fn parse_type_def_body(p: Parser) -> #(List(#(String, Term, Term, Span)), Parser) {
  parse_type_def_cases(p, [])
}

fn parse_type_def_cases(p: Parser, acc: List(#(String, Term, Term, Span))) -> #(List(#(String, Term, Term, Span)), Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  let p1 = #(tokens, pos, env, fn_, errors)
  let p2 = skip("|", p1)
  let #(tokens2, pos2, env2, fn2, errors2) = p2
  case list.drop(tokens2, pos2) {
    [Token("Punct", "}", _), ..] -> #(list.reverse(acc), p2)
    _ -> {
      // Parse constructor: #Name(pattern) -> ReturnType
      let p3 = #(tokens2, pos2, env2, fn2, errors2)
      let #(tag, p4) = expect_name_after_hash(p3)
      // Guard: if no constructor name found, we're not at a valid case.
      // Return accumulated cases to avoid infinite loop.
      case tag {
        "" -> #(list.reverse(acc), p3)
        name -> {
          let p5 = skip("(", p4)
          let #(pattern, p6) = parse_term(p5)
          let p7 = skip(")", p6)
          let p8 = skip("->", p7)
          let #(ret_type, p9) = parse_term(p8)
          let p10 = p9
          let span = current_span(p10)
          // Guard: ensure the parser advanced to avoid infinite recursion
          case p10 {
            #(tokens10, pos10, _, _, _) ->
              case pos10 == pos2 {
                True -> #(list.reverse(acc), p10)
                False ->
                  parse_type_def_cases(
                    p10,
                    [#(name, pattern, ret_type, span), ..acc],
                  )
              }
          }
        }
      }
    }
  }
}

fn expect_name_after_hash(p: Parser) -> #(String, Parser) {
  let p1 = skip("#", p)
  let #(name, p2) = expect_name_opt(p1)
  case name {
    "" -> #("", p1)
    _ -> #(name, p2)
  }
}

// Type: $Type or $Type(n)
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
          #(Ctr(name, arg, span), p5)
        }
        _ -> {
          #(Ctr(name, Rcd([], span), span), p2)
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

fn parse_rcd_fields(
  p: Parser,
  acc: List(#(String, Term)),
) -> #(List(#(String, Term)), Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> {
      let err =
        ParseError(
          span: current_span(p),
          expected: "field",
          got: "EOF",
          context: "in record",
        )
      #(list.reverse(acc), #(tokens, pos, env, fn_, [err, ..errors]))
    }
    [Token("Punct", "}", _), ..rest] -> #(
      list.reverse(acc),
      #(rest, 0, env, fn_, errors),
    )
    [Token("Eof", ..), ..] -> #(list.reverse(acc), p)
    _ -> {
      let #(name, p2) = expect_name_opt(p)
      let p3 = skip(":", p2)
      let #(value, p4) = parse_term(p3)
      let p5 = skip(",", p4)
      parse_rcd_fields(p5, [#(name, value), ..acc])
    }
  }
}

fn parse_var(p: Parser, name: String, span: Span) -> #(Term, Parser) {
  case is_keyword(name) {
    True -> {
      let e = Err("unexpected keyword: " <> name, span)
      #(e, p)
    }
    False -> {
      let #(tokens, pos, env, fn_, errors) = p
      let depth = list.length(env)
      case lookup_var(env, name, depth) {
        Ok(index) -> #(Var(index, span), p)
        Error(_) -> {
          let err =
            ParseError(
              span: span,
              expected: "variable '" <> name <> "'",
              got: "undefined",
              context: "variable not found",
            )
          #(
            Err("undefined variable: " <> name, span),
            #(tokens, pos, env, fn_, [err, ..errors]),
          )
        }
      }
    }
  }
}

fn lookup_var(
  env: List(#(String, Int)),
  name: String,
  depth: Int,
) -> Result(Int, Nil) {
  lookup_loop(env, name, 0, depth)
}

fn lookup_loop(
  env: List(#(String, Int)),
  name: String,
  idx: Int,
  depth: Int,
) -> Result(Int, Nil) {
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

// Lambda: $fn(name: Type) => body
fn parse_lambda(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("(", p)
  let #(name, p2) = expect_name_opt(p1)
  let p3 = skip(":", p2)
  let #(param_type, p4) = parse_term(p3)
  let p5 = skip(")", p4)
  let p6 = skip("=>", p5)
  let p7 = add_binding(p6, name)
  let #(body, rest) = parse_term_with_app(p7, merge(span, current_span(p7)))
  let final_span = merge(span, term_span(body))
  #(Lam([], #(name, param_type), body, final_span), rest)
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

// Match: $match arg { | pattern ? guard => body } or match arg { | pattern => body }
fn parse_match(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = case p {
    #(tokens, pos, env, fn_, errors) ->
      case list.drop(tokens, pos) {
        [Token("Op", "$", _), ..] -> skip("$", p)
        _ -> p
      }
  }
  let p2 = skip("match", p1)
  let #(arg, p3) = parse_term(p2)
  let p4 = skip("{", p3)
  let p5 = parse_cases(p4)
  let #(cases, rest) = p5
  let p6 = skip("}", rest)
  let final_span = merge(span, case_list_span(cases, span))
  #(Match(arg, cases, final_span), p6)
}

fn parse_cases(p: Parser) -> #(List(Case), Parser) {
  let #(cases, p1) = parse_cases_acc(p, [])
  #(list.reverse(cases), p1)
}

fn parse_cases_acc(p: Parser, acc: List(Case)) -> #(List(Case), Parser) {
  let span = current_span(p)
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> {
      let err =
        ParseError(
          span: current_span(p),
          expected: "case pattern",
          got: "EOF",
          context: "end of match",
        )
      #(acc, #(tokens, pos, env, fn_, [err, ..errors]))
    }
    [Token("Punct", "}", _), ..rest] -> #(
      acc,
      #(rest, 0, env, fn_, errors),
    )
    [Token("Eof", ..), ..] -> #(acc, p)
    _ -> {
      let p1 = skip("|", p)
      // Guard: if skip("|") didn't advance, we're not at a valid case.
      // Return accumulated cases to avoid infinite loop.
      case p1 {
        #(tokens1, pos1, _, _, _) ->
          case pos1 == pos {
            True -> #(acc, p1)
            False -> {
              let #(pattern, p2) = parse_pattern(p1)
              let #(guard, p3) = case p2 {
                #(tokens2, pos2, env2, fn2, errors2) ->
                  case list.drop(tokens2, pos2) {
                    [Token("Op", "?", _), ..] -> {
                      let p = #(tokens2, pos2 + 1, env2, fn2, errors2)
                      let #(g, p4) = parse_term(p)
                      #(Some(g), p4)
                    }
                    _ -> #(None, p2)
                  }
              }
              let p5 = skip("=>", p3)
              let #(body, rest_errors) = parse_term(p5)
              let case_term = CoreCase(pattern, guard, body, span)
              parse_cases_acc(rest_errors, [case_term, ..acc])
            }
          }
      }
    }
  }
}

// Let: $let name = value; body — desugars to App(Lam(name, _, body), value)
fn parse_let(p: Parser, span: Span) -> #(Term, Parser) {
  let p1 = skip("let", p)
  let #(name, p2) = expect_name_opt(p1)
  // Check for optional type annotation
  let p3 = case p2 {
    #(tokens, pos, env, fn_, errors) ->
      case list.drop(tokens, pos) {
        [Token("Punct", ":", _), ..] -> skip(":", p2)
        _ -> p2
      }
  }
  // Parse optional type or use Rcd as default
  let #(param_type, p4) = case p3 {
    #(tokens, pos, env, fn_, errors) ->
      case list.drop(tokens, pos) {
        [Token("Op", "$", _), ..] -> parse_term(p3)
        _ -> #(Rcd([], span), p3)
      }
  }
  let p5 = skip("=", p4)
  let #(value, rest) = parse_term(p5)
  let let_span = merge(span, term_span(value))
  // Check for semicolon or newline as separator
  let p6 = case rest {
    #(tokens, pos, env, fn_, errors) ->
      case list.drop(tokens, pos) {
        [Token("Punct", ";", _), ..] -> skip(";", rest)
        _ -> rest
      }
  }
  let p7 = add_binding(p6, name)
  let #(body, rest_final) = parse_term(p7)
  let body_span = merge(let_span, term_span(body))
  #(let_var(name, param_type, value, body, body_span), rest_final)
}

// Fix: $fix name = body — desugars to App(Lam(name, _, body), value)
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
    [] -> {
      let err =
        ParseError(
          span: current_span(p),
          expected: "list item",
          got: "EOF",
          context: "in list",
        )
      #(list.reverse(acc), #(tokens, pos, env, fn_, [err, ..errors]))
    }
    [Token("Punct", "]", _), ..rest] -> #(
      list.reverse(acc),
      #(rest, 0, env, fn_, errors),
    )
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
    [Token("Name", "_", _), ..] -> #(
      PAny(span),
      #(tokens, pos + 1, env, fn_, errors),
    )
    [Token("Op", "#", _), ..rest] -> {
      let p1 = #(tokens, pos + 1, env, fn_, errors)
      let #(name, p2) = expect_name_opt(p1)
      case name {
        "" -> #(PAny(span), p1)
        _ ->
          case list.drop(tokens, pos) {
            [Token("Op", "#", _), Token("Name", v, _), Token("Punct", "(", _), ..inner_rest] -> {
              let p3 = #(inner_rest, 0, env, fn_, errors)
              let #(inner, p4) = parse_pattern(p3)
              let p5 = skip(")", p4)
              let final_span = merge(span, current_span(p5))
              #(PCtr(v, inner, final_span), p5)
            }
            _ -> #(PAny(span), p1)
          }
      }
    }
    [Token("Name", v, _), ..rest] -> {
      let p1 = #(tokens, pos + 1, env, fn_, errors)
      case rest {
        [] -> {
          let p2 = add_binding(p1, v)
          #(PVar(v, span), p2)
        }
        [Token("Punct", "(", _), ..inner_rest] -> {
          let p2 = #(inner_rest, 0, env, fn_, errors)
          let #(inner, p3) = parse_pattern(p2)
          let p4 = skip(")", p3)
          let final_span = merge(span, current_span(p4))
          #(PCtr(v, inner, final_span), p4)
        }
        _ -> {
          let p2 = add_binding(p1, v)
          #(PVar(v, span), p2)
        }
      }
    }
    [Token("Punct", "(", _), Token("Punct", ")", _), ..] -> {
      let p1 = #(tokens, pos + 2, env, fn_, errors)
      #(PUnit(span), p1)
    }
    [Token("Integer", v, _), ..] -> {
      let p1 = #(tokens, pos + 1, env, fn_, errors)
      case int.parse(v) {
        Ok(value) -> #(PLit(LitInt(value), span), p1)
        Error(_) -> {
          let err =
            ParseError(
              span: span,
              expected: "integer",
              got: v,
              context: "invalid integer literal",
            )
          #(PAny(span), #(tokens, pos + 1, env, fn_, [err, ..errors]))
        }
      }
    }
    [Token("Float", v, _), ..] -> {
      let p1 = #(tokens, pos + 1, env, fn_, errors)
      case float.parse(v) {
        Ok(value) -> #(PLit(LitFloat(value), span), p1)
        Error(_) -> {
          let err =
            ParseError(
              span: span,
              expected: "float",
              got: v,
              context: "invalid float literal",
            )
          #(PAny(span), #(tokens, pos + 1, env, fn_, [err, ..errors]))
        }
      }
    }
    // Error pattern: $error
    [Token("Op", "$", _), Token("Name", "error", _), ..rest] ->
      #(PError(span), #(rest, 0, env, fn_, errors))
    // Type patterns: $Type, $Int, $Float, etc.
    [Token("Op", "$", _), Token("Name", name, _), ..rest] -> {
      case name {
        "Type" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "Int" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "Float" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "I8" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "I16" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "I32" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "I64" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "U8" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "U16" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "U32" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "U64" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "F16" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "F32" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        "F64" -> #(PType(name, span), #(rest, 0, env, fn_, errors))
        _ -> #(PAny(span), #(rest, 0, env, fn_, errors))
      }
    }
    // Type record pattern: ${field: type, ...}
    [Token("Op", "$", _), Token("Punct", "{", _), ..rest] -> {
      let p1 = #(rest, 0, env, fn_, errors)
      let #(fields, p2) = parse_pattern_fields(p1)
      let p3 = skip("}", p2)
      let final_span = merge(span, current_span(p3))
      #(PRcd(fields, final_span), p3)
    }
    // Record pattern: {field: pattern, ...}
    [Token("Punct", "{", _), ..rest] -> {
      let p1 = #(rest, 0, env, fn_, errors)
      let #(fields, p2) = parse_pattern_fields(p1)
      let p3 = skip("}", p2)
      let final_span = merge(span, current_span(p3))
      #(PRcd(fields, final_span), p3)
    }
    _ -> #(PAny(span), p)
  }
}

fn parse_pattern_fields(p: Parser) -> #(List(#(String, Pattern)), Parser) {
  parse_pattern_fields_acc(p, [])
}

fn parse_pattern_fields_acc(
  p: Parser,
  acc: List(#(String, Pattern)),
) -> #(List(#(String, Pattern)), Parser) {
  let #(tokens, pos, env, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> #(list.reverse(acc), p)
    [Token("Punct", "}", _), ..rest] -> #(
      list.reverse(acc),
      #(rest, 0, env, fn_, errors),
    )
    _ -> {
      // Parse field: either {name} or {name: pattern}
      let #(name, p2) = expect_name_opt(p)
      case name {
        "" -> {
          // Empty or invalid, just return
          #(list.reverse(acc), p)
        }
        v -> {
          // Check for {name: pattern} or {name} (sugar for {name: name})
          let p3 = case p2 {
            #(tokens, pos, env, fn_, errors) ->
              case list.drop(tokens, pos) {
                [Token("Punct", ":", _), ..] -> skip(":", p2)
                _ -> p2
              }
          }
          // Determine if this is {name} sugar (no colon, followed by } or ,)
          let current = current_span(p3)
          let #(inner, p4) = case p3 {
            #(tokens, pos, env, fn_, errors) ->
              case list.drop(tokens, pos) {
                [Token("Punct", "}", _), ..] -> {
                  let p2 = add_binding(p3, v)
                  #(PVar(v, current), p2)
                }
                [Token("Punct", ",", _), ..] -> {
                  let p2 = add_binding(skip(",", p3), v)
                  #(PVar(v, current), p2)
                }
                _ -> {
                  let #(pat, p) = parse_pattern(p3)
                  #(pat, p)
                }
              }
          }
          let p5 = skip("}", p4)
          let p6 = case p5 {
            #(tokens, pos, env, fn_, errors) ->
              case list.drop(tokens, pos) {
                [Token("Punct", ",", _), ..] -> skip(",", p5)
                _ -> p5
              }
          }
          parse_pattern_fields_acc(p6, [#(v, inner), ..acc])
        }
      }
    }
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
    Lam(_, _, _, _) -> "fn"
    App(_, _, _) -> "app"
    Pi(_, _, _, _) -> "Pi"
    Lit(_, _) -> "lit"
    Ctr(_, _, _) -> "ctr"
    Match(_, _, _) -> "match"
    Ann(_, _, _) -> "ann"
    Call(_, _, _, _, _) -> "call"
    Rcd(_, _) -> "rcd"
    Typ(_, _) -> "type"
    TypeDef(_, _, _) -> "type def"
    Err(msg, _) -> msg
  }
}

fn is_keyword(s: String) -> Bool {
  case s {
    "fn"
    | "let"
    | "in"
    | "match"
    | "case"
    | "type"
    | "of"
    | "fun"
    | "fix"
    | "hole"
    | "unit"
    | "true"
    | "false"
    | "if"
    | "then"
    | "else"
    | "import"
    | "as" -> True
    _ -> False
  }
}
