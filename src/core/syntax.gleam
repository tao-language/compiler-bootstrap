/// Core Language Parser
///
/// Parses source strings into Core AST terms as NamedTerm (string names).
/// A separate conversion pass (term_to_debruijn) converts NamedTerm to Term
/// (De Bruijn indices).
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
///   - Fixpoint: $fix name. body
import core/ast.{
  type Case, type Pattern, type NamedTerm, type Term,
  type LiteralType,
  type NamedCase,
  Case as CoreCase,
  Err, NamedAnn, NamedApp, NamedCall, NamedCase as NC,
  NamedCtr,
  NamedErr, NamedFix, NamedTypeDef,
  NamedHole, NamedLam, NamedLit, NamedLitT,
  NamedMatch, NamedPi,
  NamedRcd, NamedRcdT, NamedTyp,
  NamedVar, NamedLet,
  PAny, PAlias, PCtr, PError, PLitT, PLit,
  PTyp, PRcd, PUnit, PVar,
  let_var,
  Float as LitFloat, Int as LitInt,
  IntT, FloatT, I8T, I16T, I32T, I64T, U8T, U16T, U32T, U64T, F16T, F32T, F64T,
  term_to_debruijn, term_to_string as term_to_string_db,
}
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/base_lexer.{type Token, Token, tokenize}
import syntax/grammar.{type ParseError, ParseError}
import syntax/span.{type Span, Span, merge, single}

/// Parse a Core source string into a Term (via NamedTerm).
pub fn parse(source: String) -> #(Term, List(ParseError)) {
  let tokens = tokenize(source)
  parse_tokens(tokens, "")
}

/// Parse tokens into a Core term (NamedTerm → Term via term_to_debruijn).
pub fn parse_tokens(
  tokens: List(Token),
  filename: String,
) -> #(Term, List(ParseError)) {
  let state = #(tokens, 0, filename, [])
  let span = single(filename, 1, 1)
  let #(named, acc, state2) = parse_tokens_acc(state, [])
  let #(tokens2, pos2, _, errs) = state2
  // Convert NamedTerm → Term, wrapping in accumulated definitions
  let folded = fold_named_terms(named, acc)
  let term = term_to_debruijn(folded)
  case term {
    Err(msg, _) -> #(Err(msg, span), errs)
    t -> {
      let rest = try_peek(tokens2, pos2)
      case rest {
        Error(_) -> #(t, errs)
        Ok(Token(kind: "Eof", value: "", span: _)) -> #(t, errs)
        Ok(Token(kind: kind, value: value, span: span)) -> {
          let err =
            ParseError(
              span: span,
              expected: "end of input",
              got: value,
              context: "unexpected token",
              rule: "parse_tokens_acc",
              surrounding: surrounding_tokens(tokens2, pos2),
            )
          #(t, [err, ..errs])
        }
      }
    }
  }
}

/// Check if two spans are on the same line.
/// Used to determine if tokens are separated by spaces (same line) vs newlines.
/// span1 is the end of the current term, span2 is the start of the next token.
fn same_line(span1: Span, span2: Span) -> Bool {
  span1.end_line == span2.start_line
}

fn is_continuation_token(token: Token) -> Bool {
  case token {
    Token("Punct", v, _) -> case v {
      ":" | "." | "," | "(" | ")" | "}" | "]" -> True
      _ -> False
    }
    Token("Op", v, _) -> case v {
      ":" | "." | "," | "~" | "-" | ">" | "=>" -> True
      _ -> False
    }
    _ -> False
  }
}

/// Parse sequential expressions, returning the last expression as the result
fn parse_tokens_acc(p: Parser, acc: List(NamedTerm)) -> #(NamedTerm, List(NamedTerm), Parser) {
  let #(term, p2) = parse_app(p, single("", 0, 0))
  let #(tokens2, pos2, _, _) = p2
  let rest = try_peek(tokens2, pos2)
  case rest {
    Error(_) -> #(term, acc, p2)
    Ok(Token(kind: "Eof", value: "", span: _)) -> #(term, acc, p2)
    Ok(Token(kind: _, value: _, span: _)) -> {
      let #(tokens3, pos3, _, _) = p2
      case list.drop(tokens3, pos3) {
        [t, ..] -> case is_continuation_token(t) {
          True -> #(term, acc, p2)
          False -> parse_tokens_acc(p2, [term, ..acc])
        }
        [] -> #(term, acc, p2)
      }
    }
  }
}

/// Fold accumulated NamedTerms into a single term by wrapping in let chains.
/// The acc list is in reverse order (first parsed at head), so we reverse it
/// and wrap each one as: let name = value; rest
fn fold_named_terms(named: NamedTerm, acc: List(NamedTerm)) -> NamedTerm {
  case acc {
    [] -> named
    [first, ..rest] -> {
      // Extract the name from the first term if it's a let binding
      let name = case first {
        NamedLet(n, _, _, _, _) -> case n {
          "" -> "_acc_" <> int.to_string(list.length(acc))
          n -> n
        }
        _ -> "_acc_" <> int.to_string(list.length(acc))
      }
      fold_named_terms(
        NamedLet(name, NamedRcd([], single("", 0, 0)), first, named, single("", 0, 0)),
        rest
      )
    }
  }
}

type Parser =
  #(List(Token), Int, String, List(ParseError))

fn try_peek(tokens: List(Token), pos: Int) -> Result(Token, List(ParseError)) {
  case list.drop(tokens, pos) {
    [] -> Error([])
    [t, ..] -> Ok(t)
  }
}

fn current_span(p: Parser) -> Span {
  let #(tokens, pos, _, _) = p
  case list.drop(tokens, pos) {
    [] -> single(p.2, 1, 1)
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

/// Get surrounding tokens for error reporting: 3 before and 3 after position.
fn surrounding_tokens(tokens: List(Token), pos: Int) -> List(Token) {
  let start = case pos - 3 {
    n if n < 0 -> 0
    n -> n
  }
  let before = tokens |> list.drop(start) |> list.take(pos - start)
  let after = tokens |> list.drop(pos) |> list.take(3)
  list.append(before, after)
}

/// Convert a token to a human-readable string for error messages.
fn token_to_string(tok: Token) -> String {
  case tok {
    Token("Name", v, _) -> "Name '" <> v <> "'"
    Token("Op", v, _) -> "Op '" <> v <> "'"
    Token("Punct", v, _) -> "Punct '" <> v <> "'"
    Token("Integer", v, _) -> "Integer '" <> v <> "'"
    Token("Float", v, _) -> "Float '" <> v <> "'"
    Token("String", v, _) -> "String '" <> v <> "'"
    Token("Eof", _, _) -> "EOF"
    Token("Keyword", v, _) -> "Keyword '" <> v <> "'"
    Token(_, v, _) -> v
  }
}

fn skip(kind: String, p: Parser) -> Parser {
  let #(tokens, pos, fn_, errors) = p
  case kind {
    "->" -> {
      case list.drop(tokens, pos) {
        [Token("Op", "-", _), Token("Op", ">", _), ..] -> #(
          tokens,
          pos + 2,
          fn_,
          errors,
        )
        _ -> {
          let got = case list.drop(tokens, pos) {
            [Token(k, v, _), ..] -> k <> " '" <> v <> "'"
            [] -> "end of input"
          }
          let err = ParseError(
            span: span_for_pos(tokens, pos),
            expected: "->",
            got: got,
            context: "in lambda pattern",
            rule: "skip",
            surrounding: surrounding_tokens(tokens, pos),
          )
          #(tokens, pos, fn_, [err, ..errors])
        }
      }
    }
    "=>" -> {
      case list.drop(tokens, pos) {
        [Token("Punct", "=", _), Token("Op", ">", _), ..] -> #(
          tokens,
          pos + 2,
          fn_,
          errors,
        )
        _ -> {
          let got = case list.drop(tokens, pos) {
            [Token(k, v, _), ..] -> k <> " '" <> v <> "'"
            [] -> "end of input"
          }
          let err = ParseError(
            span: span_for_pos(tokens, pos),
            expected: "=>",
            got: got,
            context: "in lambda pattern",
            rule: "skip",
            surrounding: surrounding_tokens(tokens, pos),
          )
          #(tokens, pos, fn_, [err, ..errors])
        }
      }
    }
    _ -> {
      case list.drop(tokens, pos) {
        [Token(k, _, _), ..] if k == kind -> #(
          tokens,
          pos + 1,
          fn_,
          errors,
        )
        [Token("Punct", pval, _), ..] if pval == kind -> #(
          tokens,
          pos + 1,
          fn_,
          errors,
        )
        [Token("Op", opval, _), ..] if opval == kind -> #(
          tokens,
          pos + 1,
          fn_,
          errors,
        )
        [Token("Name", nval, _), ..] if nval == kind -> #(
          tokens,
          pos + 1,
          fn_,
          errors,
        )
        _ -> p
      }
    }
  }
}

fn expect_name_opt(p: Parser) -> #(String, Parser) {
  let #(tokens, pos, fn_, errors) = p
  case list.drop(tokens, pos) {
    [Token("Name", v, _), ..] -> #(v, #(tokens, pos + 1, fn_, errors))
    _ -> #("", p)
  }
}

fn parse_term(p: Parser) -> #(NamedTerm, Parser) {
  let #(tokens, pos, fn_, errors) = p
  let span = current_span(p)
  case list.drop(tokens, pos) {
    [] -> {
      let e = NamedErr("unexpected end of input", span)
      #(e, p)
    }

    // Integer and float literals
    [Token("Integer", v, _), ..] ->
      case int.parse(v) {
        Ok(value) -> #(
          NamedLit(LitInt(value), span),
          #(tokens, pos + 1, fn_, errors),
        )
        Error(_) -> {
          let e = NamedErr("invalid integer: " <> v, span)
          #(e, #(tokens, pos + 1, fn_, errors))
        }
      }
    [Token("Float", v, _), ..] ->
      case float.parse(v) {
        Ok(value) -> #(
          NamedLit(LitFloat(value), span),
          #(tokens, pos + 1, fn_, errors),
        )
        Error(_) -> {
          let e = NamedErr("invalid float: " <> v, span)
          #(e, #(tokens, pos + 1, fn_, errors))
        }
      }

    // String literals - error
    [Token("String", v, _), ..] -> {
      let e = NamedErr("string literal not supported: " <> v, span)
      #(e, #(tokens, pos + 1, fn_, errors))
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
      #(NamedHole(parsed_id, new_span), #(tokens, new_pos, fn_, errors))
    }

    // Record type syntax: ${field: type, ...} (record type with optional defaults)
    [Token("Op", "$", _), Token("Punct", "{", _), ..rest] -> {
      let p1 = #(rest, 0, fn_, errors)
      let #(fields, p2) = parse_rcd_type_fields(p1, [])
      let p3 = skip("}", p2)
      #(NamedRcdT(fields, span), p3)
    }
    // Prefixed tokens: $ followed by keyword
    [Token("Op", "$", _), Token("Punct", ")", _), ..rest] ->
      #(NamedRcd([], span), #(rest, 0, fn_, errors))
    [Token("Op", "$", _), Token("Name", "fn", _), ..rest] ->
      parse_lambda(#(rest, 0, fn_, errors), span)
    [Token("Op", "$", _), Token("Name", "let", _), ..rest] ->
      parse_let(#(rest, 0, fn_, errors), span)
    [Token("Op", "$", _), Token("Name", "match", _), ..] ->
      parse_match(#(tokens, pos, fn_, errors), span)
    // Also support plain match (without $)
    [Token("Name", "match", _), ..] ->
      parse_match(#(tokens, pos, fn_, errors), span)
    [Token("Op", "$", _), Token("Name", "fix", _), ..rest] ->
      parse_fix(#(rest, 0, fn_, errors), span)
    // Type definition: $type { | #C(args) -> ReturnType } or $type<>(...)
    [Token("Op", "$", _), Token("Name", "type", _), ..rest] ->
      parse_type_def(#(rest, 0, fn_, errors), span)
    // Error term: $error "message" or $error (without message)
    [Token("Op", "$", _), Token("Name", "error", _), Token("String", msg, _), ..rest] ->
      #(NamedErr(msg, span), #(rest, 0, fn_, errors))
    [Token("Op", "$", _), Token("Name", "error", _), ..rest] ->
      #(NamedErr("error", span), #(rest, 0, fn_, errors))
    // Pi type: $pi<a: Type>(a) -> a
    [Token("Op", "$", _), Token("Name", "pi", _), ..rest] ->
      parse_pi(#(rest, 0, fn_, errors), span)
    // Built-in type values: $Type, $Int, $Float, $I32, etc.
    [Token("Op", "$", _), Token("Name", name, _), ..rest] ->
      case name {
        // $Type or $Type<N> where N is an integer literal or variable
        "Type" -> {
          // Check for optional <N> parameter and consume it
          let result = case rest {
            [Token("Op", "<", _), Token("Integer", v, _), Token("Op", ">", _), ..rest2] -> {
              let lvl = case int.parse(v) {
                Ok(n) -> n
                Error(_) -> 0
              }
              #(NamedTyp(lvl, span), #(rest2, 0, fn_, errors))
            }
            [Token("Op", "<", _), Token("Name", v, _), Token("Op", ">", _), ..rest2] -> {
              // $Type<x> — type variable
              let lvl = case int.parse(v) {
                Ok(n) -> n
                Error(_) -> 0
              }
              #(NamedTyp(lvl, span), #(rest2, 0, fn_, errors))
            }
            _ -> #(NamedTyp(0, span), #(rest, 0, fn_, errors))
          }
          result
        }
        // Literal types: $Int, $Float, $I32, $I64, $U8-$U64, $F16-$F64
        "Int" -> #(NamedLitT(t: IntT, span: span), #(rest, 0, fn_, errors))
        "Float" -> #(NamedLitT(t: FloatT, span: span), #(rest, 0, fn_, errors))
        "I8" -> #(NamedLitT(t: I8T, span: span), #(rest, 0, fn_, errors))
        "I16" -> #(NamedLitT(t: I16T, span: span), #(rest, 0, fn_, errors))
        "I32" -> #(NamedLitT(t: I32T, span: span), #(rest, 0, fn_, errors))
        "I64" -> #(NamedLitT(t: I64T, span: span), #(rest, 0, fn_, errors))
        "U8" -> #(NamedLitT(t: U8T, span: span), #(rest, 0, fn_, errors))
        "U16" -> #(NamedLitT(t: U16T, span: span), #(rest, 0, fn_, errors))
        "U32" -> #(NamedLitT(t: U32T, span: span), #(rest, 0, fn_, errors))
        "U64" -> #(NamedLitT(t: U64T, span: span), #(rest, 0, fn_, errors))
        "F16" -> #(NamedLitT(t: F16T, span: span), #(rest, 0, fn_, errors))
        "F32" -> #(NamedLitT(t: F32T, span: span), #(rest, 0, fn_, errors))
        "F64" -> #(NamedLitT(t: F64T, span: span), #(rest, 0, fn_, errors))
        _ -> #(NamedCtr(name, NamedHole(0, span), span), #(rest, 0, fn_, errors))
      }
    // FFI builtin calls: % followed by function name
    [Token("Op", "%", _), Token("Name", v, _), ..rest] ->
      parse_ffi_call(#(rest, 0, fn_, errors), v, span)
    // Keywords and prefixed tokens
    [Token("Name", v, _), ..] -> {
      case v {
        "hole" -> #(NamedHole(0, span), #(tokens, pos + 1, fn_, errors))
        "unit" -> #(NamedRcd([], span), #(tokens, pos + 1, fn_, errors))
        "type" -> #(NamedTyp(0, span), #(tokens, pos + 1, fn_, errors))
        "true" -> #(NamedRcd([], span), #(tokens, pos + 1, fn_, errors))
        "fun" -> parse_pi(#(tokens, pos + 1, fn_, errors), span)
        _ -> {
          let #(var_term, var_rest) = parse_var(#(tokens, pos + 1, fn_, errors), v, span)
          parse_app_chain(var_rest, var_term, span)
        }
      }
    }

    // Operators
    [Token("Op", v, _), ..] -> {
      case v {
        "#" -> {
          let span = current_span(p)
          let #(ctor, p_rest) = parse_ctr(#(tokens, pos + 1, fn_, errors), span)
          parse_app_chain(p_rest, ctor, span)
        }
        "-" -> {
          let p = #(tokens, pos + 1, fn_, errors)
          let #(body, p2) = parse_term(p)
          let app_span = merge(span, term_span_named(body))
          let e =
            NamedErr("negation not supported: " <> term_to_string_named(body), app_span)
          #(e, p2)
        }
        "!" -> {
          let p = #(tokens, pos + 1, fn_, errors)
          let #(body, p2) = parse_term(p)
          let app_span = merge(span, term_span_named(body))
          let e = NamedErr("not not supported: " <> term_to_string_named(body), app_span)
          #(e, p2)
        }
        _ -> {
          let e = NamedErr("unexpected operator: " <> v, span)
          #(e, #(tokens, pos + 1, fn_, errors))
        }
      }
    }

    // Parenthesized expressions: (expr) or (term : Type)
    // Also handles () as unit (Rcd with empty fields)
    [Token("Punct", "(", _), Token("Punct", ")", _), ..rest] -> #(
      NamedRcd([], span),
      #(rest, 0, fn_, errors),
    )
    [Token("Punct", "(", _), ..rest] -> {
      let p = #(rest, 0, fn_, errors)
      let #(inner, p2) = parse_term(p)
      let p3 = skip(")", p2)
      #(inner, p3)
    }

    // Punctuation
    [Token("Punct", "[", _), ..rest] ->
      parse_list(#(rest, 0, fn_, errors), span)
    [Token("Punct", "{", _), ..rest] ->
      parse_rcd(#(rest, 0, fn_, errors), span)
    [Token("Eof", ..), ..] -> {
      let e = NamedErr("unexpected end of input", span)
      #(e, p)
    }
    [Token(_, v, _), ..] -> {
      let e = NamedErr("unexpected token: " <> v, span)
      #(e, #(tokens, pos + 1, fn_, errors))
    }
  }
}

/// Get span from a NamedTerm for error reporting.
fn term_span_named(term: NamedTerm) -> Span {
  case term {
    NamedVar(_, span) -> span
    NamedHole(_, span) -> span
    NamedLam(_, _, _, span) -> span
    NamedApp(_, _, span) -> span
    NamedPi(_, _, _, span) -> span
    NamedLit(_, span) -> span
    NamedCtr(_, _, span) -> span
    NamedMatch(_, _, span) -> span
    NamedAnn(_, _, span) -> span
    NamedCall(_, _, _, span) -> span
    NamedRcd(_, span) -> span
    NamedRcdT(_, span) -> span
    NamedTyp(_, span) -> span
    NamedTypeDef(_, _, _, span) -> span
    NamedLitT(_, span) -> span
    NamedFix(_, _, span) -> span
    NamedErr(_, span) -> span
    NamedLet(_, _, _, _, span) -> span
  }
}

/// Format a NamedTerm for debugging / display.
fn term_to_string_named(term: NamedTerm) -> String {
  case term {
    NamedVar(name, _) -> name
    NamedHole(id, _) -> "?" <> int.to_string(id)
    NamedLam(implicits, #(name, param_type), func_body, _) -> {
      let implicit_str = case implicits {
        [] -> ""
        _ ->
          "<"
          <> list.fold(
            list.map(implicits, fn(i) { i.0 <> ": " <> term_to_string_named(i.1) }),
            "",
            fn(acc, s) {
              case acc {
                "" -> s
                _ -> acc <> ", " <> s
              }
            },
          )
          <> ">"
      }
      "$fn"
      <> implicit_str
      <> "("
      <> name
      <> ": "
      <> term_to_string_named(param_type)
      <> ") => "
      <> term_to_string_named(func_body)
    }
    NamedApp(fun, arg, _) ->
      "(" <> term_to_string_named(fun) <> " " <> term_to_string_named(arg) <> ")"
    NamedPi(implicits, #(name, domain), codomain, _) -> {
      let implicit_str = case implicits {
        [] -> ""
        _ ->
          "<"
          <> list.fold(
            list.map(implicits, fn(i) { i.0 <> ": " <> term_to_string_named(i.1) }),
            "",
            fn(acc, s) {
              case acc {
                "" -> s
                _ -> acc <> ", " <> s
              }
            },
          )
          <> ">"
      }
      "$pi"
      <> implicit_str
      <> "("
      <> name
      <> ": "
      <> term_to_string_named(domain)
      <> ") -> "
      <> term_to_string_named(codomain)
    }
    NamedLit(LitInt(value), _) -> int.to_string(value)
    NamedLit(LitFloat(value), _) -> float.to_string(value)
    NamedCtr(tag, arg, _) -> "#" <> tag <> "(" <> term_to_string_named(arg) <> ")"
    NamedMatch(arg, cases, _) ->
      "$match ("
      <> term_to_string_named(arg)
      <> ") {"
      <> list.fold(cases, "", fn(acc, c) {
        acc <> "\n  | " <> case_to_string_named(c)
      })
      <> "\n}"
    NamedAnn(term, type_, _) ->
      term_to_string_named(term) <> " : " <> term_to_string_named(type_)
    NamedCall(name, args, return_type, _) ->
      "%"
      <> name
      <> "<"
      <> term_to_string_named(return_type)
      <> ">(" 
      <> list.fold(args, "", fn(acc, ta) {
        let arg_str = term_to_string_named(ta.0) <> ": " <> term_to_string_named(ta.1)
        case acc {
          "" -> arg_str
          _ -> acc <> ", " <> arg_str
        }
      })
      <> ")"
    NamedRcd(fields, _) ->
        "{"
        <> list.fold(fields, "", fn(acc, f) {
          case acc {
            "" -> f.0 <> ": " <> term_to_string_named(f.1)
            _ -> acc <> ", " <> f.0 <> ": " <> term_to_string_named(f.1)
          }
        })
        <> "}"
    NamedRcdT(fields, _) ->
      "${"
      <> list.fold(fields, "", fn(acc, f) {
        let field_str = f.0 <> ": " <> term_to_string_named(f.1)
        let field_with_default = case f.2 {
          Some(default_) -> field_str <> " = " <> term_to_string_named(default_)
          None -> field_str
        }
        case acc {
          "" -> field_with_default
          _ -> acc <> ", " <> field_with_default
        }
      })
      <> "}"
    NamedTyp(universe, _) -> "$Type<" <> int.to_string(universe) <> ">"
    NamedLitT(ltype, _) -> literal_type_to_string_named(ltype)
    NamedErr(message, _) -> "<error: " <> message <> ">"
    NamedFix(name, body, _) -> "$fix " <> name <> ". " <> term_to_string_named(body)
    NamedLet(name, param_type, value, body, _) ->
      "$let " <> name <> " = " <> term_to_string_named(value) <> "; " <> term_to_string_named(body)
    NamedTypeDef(_, _, constructors, _) -> {
      "$type { "
      <> list.fold(constructors, "", fn(acc, c) {
        let #(tag, #(bindings, self_ty, return_type), span) = c
        let bindings_str = case bindings {
          [] -> ""
          _ -> "@" <> list.fold(bindings, "", fn(a, b) {
            case a {
              "" -> b
              _ -> a <> " " <> b
            }
          }) <> ". "
        }
        case acc {
          "" ->
            "#"
            <> tag
            <> "("
            <> bindings_str
            <> term_to_string_named(self_ty)
            <> " -> "
            <> term_to_string_named(return_type)
            <> ")"
          _ ->
            acc
            <> " | "
            <> "#"
            <> tag
            <> "("
            <> bindings_str
            <> term_to_string_named(self_ty)
            <> " -> "
            <> term_to_string_named(return_type)
            <> ")"
        }
      })
      <> " }"
    }
  }
}

fn case_to_string_named(c: NamedCase) -> String {
  let body_str = term_to_string_named(c.body)
  case c.guard {
    Some(guard) -> body_str <> " ? " <> term_to_string_named(guard)
    None -> body_str
  }
}

fn literal_type_to_string_named(ltype: LiteralType) -> String {
  case ltype {
    IntT -> "$Int"
    FloatT -> "$Float"
    I8T -> "$I8"
    I16T -> "$I16"
    I32T -> "$I32"
    I64T -> "$I64"
    U8T -> "$U8"
    U16T -> "$U16"
    U32T -> "$U32"
    U64T -> "$U64"
    F16T -> "$F16"
    F32T -> "$F32"
    F64T -> "$F64"
  }
}

/// Parse a term followed by Haskell-style application arguments.
/// `f x y z` becomes `App(App(App(f, x), y), z)`.
/// Parenthesized terms like `f (g x)` are also supported.
/// Stops at keywords (fun, let, match, etc.) and operators (~, :).
/// Uses the term's own span for same-line checks in parse_app_chain.
fn parse_app(p: Parser, span: Span) -> #(NamedTerm, Parser) {
  let #(term, rest) = parse_term(p)
  parse_app_chain(rest, term, term_span_named(term))
}

/// Recursively apply arguments to a term (Haskell-style).
/// Applications only continue on the same line (spaces, not newlines).
fn parse_app_chain(p: Parser, fun: NamedTerm, span: Span) -> #(NamedTerm, Parser) {
  let #(tokens, pos, fn_, errors) = p
  let rest = list.drop(tokens, pos)
  
  // Check if next token is on the same line - if not, stop application
  case rest {
    [] -> #(fun, p)
    [Token(_, _, next_span), ..] ->
      case same_line(span, next_span) {
        False -> #(fun, p)  // Newline separates expressions
        True -> {
          case rest {
            // Keywords stop application
            [Token("Name", v, _), ..] -> case v {
              "fun" | "let" | "match" | "fix" | "type" | "hole" | "unit" | "true" | "false" ->
                #(fun, p)
              _ -> {
                // Variable name as application argument
                let arg_span = current_span(p)
                let p1 = #(tokens, pos + 1, fn_, errors)
                let #(arg, rest2) = parse_var(p1, v, arg_span)
                let app_span = merge(span, term_span_named(arg))
                let app = NamedApp(fun, arg, app_span)
                parse_app_chain(rest2, app, app_span)
              }
            }
            // Match/guard operator continues the chain
            [Token("Op", "~", _), ..rest] -> {
              let p_rhs = #(rest, 0, fn_, errors)
              let #(rhs, p2) = parse_pattern(p_rhs)
              let match_span = merge(span, term_span_named(fun))
              let match_term = NamedMatch(
                fun,
                [
                  NC(rhs, None, NamedCtr("True", NamedRcd([], match_span), match_span), match_span),
                  NC(PAny(match_span), None, NamedCtr("False", NamedRcd([], match_span), match_span), match_span),
                ],
                match_span,
              )
              parse_app_chain(p2, match_term, match_span)
            }
            // Annotation operator continues the chain
            [Token("Punct", ":", _), ..rest] -> {
              let p1 = #(rest, 0, fn_, errors)
              let #(type_, p2) = parse_term(p1)
              let ann_span = merge(span, term_span_named(type_))
              let annotated = NamedAnn(fun, type_, ann_span)
              parse_app_chain(p2, annotated, ann_span)
            }

            // Parenthesized term as application argument
            [Token("Punct", "(", _), ..] -> {
              let #(paren_term, p2) = parse_term(#(tokens, pos, fn_, errors))
              let app_span = merge(span, term_span_named(paren_term))
              let app = NamedApp(fun, paren_term, app_span)
              parse_app_chain(p2, app, app_span)
            }
            // Prefixed tokens - check if it's an FFI call or type prefix
            [Token("Op", "$", _), ..] ->
              #(fun, p)
            [Token("Op", "%", _), ..rest] -> {
              // FFI call as application argument: f %call<a, b>(arg1, arg2)
              let #(ffi_call, p2) = parse_term(#(tokens, pos, fn_, errors))
              let app_span = merge(span, term_span_named(ffi_call))
              let app = NamedApp(fun, ffi_call, app_span)
              parse_app_chain(p2, app, app_span)
            }
            // Constructor as application argument (same line only)
            [Token("Op", "#", _), ..] -> {
              let #(ctor_term, p2) = parse_term(#(tokens, pos, fn_, errors))
              let app_span = merge(span, term_span_named(ctor_term))
              let app = NamedApp(fun, ctor_term, app_span)
              parse_app_chain(p2, app, app_span)
            }
            // Integer and float literals as application arguments (same line only)
            [Token("Integer", _, _), ..] -> {
              let #(int_term, p2) = parse_term(#(tokens, pos, fn_, errors))
              let app_span = merge(span, term_span_named(int_term))
              let app = NamedApp(fun, int_term, app_span)
              parse_app_chain(p2, app, app_span)
            }
            [Token("Float", _, _), ..] -> {
              let #(float_term, p2) = parse_term(#(tokens, pos, fn_, errors))
              let app_span = merge(span, term_span_named(float_term))
              let app = NamedApp(fun, float_term, app_span)
              parse_app_chain(p2, app, app_span)
            }
            // Anything else stops application
            _ ->
              #(fun, p)
          }
        }
      }
  }
}

// FFI call: %name<ReturnType>(arg: Type, arg: Type)
// The return type uses angle brackets to avoid ambiguity with Pi types.
fn parse_ffi_call(p: Parser, name: String, _span: Span) -> #(NamedTerm, Parser) {
  // Parse optional return type: <ReturnType>
  let p_with_ret = case p {
    #(tokens, pos, fn_, errors) ->
      case list.drop(tokens, pos) {
        [Token("Op", "<", _), ..] -> {
          let p1 = skip("<", p)
          let #(ret_type, p2) = parse_term(p1)
          let p3 = skip(">", p2)
          #(ret_type, p3)
        }
        _ -> #(NamedHole(-1, single("", 0, 0)), p)
      }
  }
  let #(ret_type, p1) = p_with_ret
  // Parse parenthesized typed arguments
  let p2 = skip("(", p1)
  let #(typed_args, p3) = parse_typed_arg_list(p2)
  let p4 = skip(")", p3)
  let final_span = current_span(p4)
  #(NamedCall(name, typed_args, ret_type, final_span), p4)
}

// Parse a comma-separated list of typed arguments (arg: Type, arg: Type)
fn parse_typed_arg_list(p: Parser) -> #(List(#(NamedTerm, NamedTerm)), Parser) {
  parse_typed_arg_list_acc(p, [])
}

fn parse_typed_arg_list_acc(p: Parser, acc: List(#(NamedTerm, NamedTerm))) -> #(List(#(NamedTerm, NamedTerm)), Parser) {
  let #(tokens, pos, fn_, errors) = p
  let p1 = #(tokens, pos, fn_, errors)
  let p2 = skip(",", p1)
  let #(tokens2, pos2, _fn2, _errors2) = p2
  case list.drop(tokens2, pos2) {
    [Token("Punct", ")", _), ..] -> #(list.reverse(acc), p2)
    _ -> {
      let #(arg, p4) = parse_term(p2)
      // Guard: if parse_term didn't advance, we're not at a valid argument.
      // Return accumulated args to avoid infinite loop.
      case p4 {
        #(tokens4, pos4, fn4, errors4) ->
          case pos4 == pos2 {
            True -> #(list.reverse(acc), p4)
            False -> {
              let p5 = #(tokens4, pos4, fn4, errors4)
              // Check if there's a type annotation after the argument
              let p6 = skip(":", p5)
              let #(ttokens, tpos, tfn_, terrors) = p6
              case tpos > pos4 {
                True -> {
                  // Type annotation present, parse the type
                  let p7 = #(ttokens, tpos, tfn_, terrors)
                  let #(type_, p8) = parse_term(p7)
                  parse_typed_arg_list_acc(p8, [#(arg, type_), ..acc])
                }
                False -> {
                  // No type annotation - use Hole(-1) as default type (uninstantiated)
                  // Check if next token is , or ) to continue/stop
                  case list.drop(p5.0, p5.1) {
                    [Token("Punct", ",", _), ..] -> {
                      // Continue with more arguments
                      parse_typed_arg_list_acc(p5, [#(arg, NamedHole(-1, single("", 0, 0))), ..acc])
                    }
                    [Token("Punct", ")", _), ..] -> {
                      // No more arguments
                      parse_typed_arg_list_acc(p5, [#(arg, NamedHole(-1, single("", 0, 0))), ..acc])
                    }
                    _ -> {
                      // Unknown token, use Hole as default
                      parse_typed_arg_list_acc(p5, [#(arg, NamedHole(-1, single("", 0, 0))), ..acc])
                    }
                  }
                }
              }
            }
          }
      }
    }
  }
}

// Type definition: $type { | #C(args) -> ReturnType } or $type<>(...)
fn parse_type_def(p: Parser, span: Span) -> #(NamedTerm, Parser) {
  let #(tokens, pos, fn_, errors) = p
  case list.drop(tokens, pos) {
    // $type<params> { ... } -> type with type params
    [Token("Op", "<", _), ..] -> {
      let p1 = skip("<", p)
      let #(params, p2) = parse_type_params(p1)
      let p3 = skip(">", p2)
      let p4 = skip("{", p3)
      let #(td_body, p5) = parse_type_def_body(p4)
      let p6 = skip("}", p5)
      // Use the span of the closing } for the type def, not the next token
      let td_span = current_span(p5)
      let type_def = NamedTypeDef("", params, td_body, td_span)
      parse_type_def_body_with_body(p6, type_def)
    }
    // $type { ... } -> type without params
    [Token("Punct", "{", _), ..rest] -> {
      let p1 = #(rest, 0, fn_, errors)
      let #(td_body, p2) = parse_type_def_body(p1)
      let p3 = skip("}", p2)
      // Use the span of the closing } for the type def, not the next token
      let td_span = current_span(p2)
      let type_def = NamedTypeDef("", [], td_body, td_span)
      parse_type_def_body_with_body(p3, type_def)
    }
    // $type alone -> universe type
    _ -> #(NamedTyp(0, span), p)
  }
}

/// Parse type parameters: a: $Type, b: $Type
fn parse_type_params(p: Parser) -> #(List(#(String, NamedTerm)), Parser) {
  parse_type_params_acc(p, [])
}

fn parse_type_params_acc(p: Parser, acc: List(#(String, NamedTerm))) -> #(List(#(String, NamedTerm)), Parser) {
  let #(name, p1) = expect_name_opt(p)
  case name {
    "" -> #(list.reverse(acc), p)
    _ -> {
      let p2 = skip(":", p1)
      let #(param_type, p3) = parse_term(p2)
      let p4 = case p3 {
        #(tokens, pos, _, _) ->
          case list.drop(tokens, pos) {
            [Token("Punct", ",", _), ..rest] -> #(rest, 0, p3.2, p3.3)
            _ -> p3
          }
      }
      let new_acc = [ #(name, param_type), ..acc ]
      parse_type_params_acc(p4, new_acc)
    }
  }
}

/// Parse a type definition followed by a body expression.
/// The type definition is stored in an environment and the body is returned.
fn parse_type_def_body_with_body(
  p: Parser,
  type_def: NamedTerm,
) -> #(NamedTerm, Parser) {
  let #(tokens, pos, _, _) = p
  let remaining = list.drop(tokens, pos)
  case remaining {
    [] -> {
      #(type_def, p)
    }
    [Token("Eof", ..), ..] -> {
      #(type_def, p)
    }
    [Token("Punct", v, span), ..] -> {
      case v {
        // Tokens that signal end of type definition (no body follows)
        ":" | "." | "," | ";" | "]" | ")" | "}" | "{" | "|" -> {
          #(type_def, p)
        }
        // Any other punct token could start an expression, check line
        _ -> {
          let next = try_peek(tokens, pos)
          case next {
            Ok(Token(_, _, next_span)) -> case same_line(span, next_span) {
              True -> {
                let #(body, rest) = parse_term(p)
                #(body, rest)
              }
              False -> #(type_def, p)
            }
            Error(_) -> #(type_def, p)
          }
        }
      }
    }
    [Token("Op", v, span), ..] -> {
      case v {
        // Tokens that signal end of type definition (no body follows)
        ":" | "." | "," | "~" | "(" | "-" | ">" | "=>" | "$" | "{" | "#" -> {
          #(type_def, p)
        }
        _ -> {
          let next = try_peek(tokens, pos)
          case next {
            Ok(Token(_, _, next_span)) -> case same_line(span, next_span) {
              True -> {
                let #(body, rest) = parse_term(p)
                #(body, rest)
              }
              False -> #(type_def, p)
            }
            Error(_) -> #(type_def, p)
          }
        }
      }
    }
    _ -> {
      let #(body, rest) = parse_term(p)
      #(body, rest)
    }
  }
}

// Parse type definition body: { | @bindings #C(arg) -> ReturnType }
// The @bindings are constructor-bound variables solved by unification.
fn parse_type_def_body(p: Parser) -> #(List(#(String, #(List(String), NamedTerm, NamedTerm), Span)), Parser) {
  let #(cases, rest) = parse_type_def_cases(p, [])
  case cases {
    [] -> #(cases, rest)
    [_] -> #(cases, rest)
    _ -> #(cases, rest)
  }
}

fn parse_type_def_cases(p: Parser, acc: List(#(String, #(List(String), NamedTerm, NamedTerm), Span))) -> #(List(#(String, #(List(String), NamedTerm, NamedTerm), Span)), Parser) {
  let #(tokens, pos, fn_, errors) = p
  let p1 = #(tokens, pos, fn_, errors)
  let p2 = skip("|", p1)
  let #(tokens2, pos2, fn2, errors2) = p2
  case list.drop(tokens2, pos2) {
    [Token("Punct", "}", _), ..] -> #(list.reverse(acc), p2)
    [Token("Eof", ..), ..] -> #(list.reverse(acc), p2)
    _ -> {
      // Parse optional @bindings: @x y z.
      let p3 = #(tokens2, pos2, fn2, errors2)
      let #(bindings, p4) = parse_type_def_bindings(p3)
      // Parse constructor: #Name(pattern) -> ReturnType
      let #(tag, p5) = expect_name_after_hash(p4)
      // Guard: if no constructor name found, we're not at a valid case.
      // Return accumulated cases to avoid infinite loop.
      case tag {
        "" -> #(list.reverse(acc), p3)
        name -> {
          let p6 = skip("(", p5)
          let #(pattern, p7) = parse_term(p6)
          let p8 = skip(")", p7)
          let p9 = skip("->", p8)
          let #(ret_type, p10) = parse_term(p9)
          let span = current_span(p10)
          // Guard: ensure the parser advanced to avoid infinite recursion.
          // Check if p10's token list is the same as tokens2 and position advanced.
          case p10 {
            #(t10, pos10, _, _) ->
              case t10 == tokens2 && pos10 > pos2 {
                True ->
                  parse_type_def_cases(
                    p10,
                    [#(name, #(bindings, pattern, ret_type), span), ..acc],
                  )
                False ->
                  parse_type_def_cases(
                    p10,
                    [#(name, #(bindings, pattern, ret_type), span), ..acc],
                  )
              }
          }
        }
      }
    }
  }
}

/// Parse optional @bindings: @x y z.
/// Returns the list of binding names (empty if no @ found).
fn parse_type_def_bindings(p: Parser) -> #(List(String), Parser) {
  let #(tokens, pos, fn_, errors) = p
  case list.drop(tokens, pos) {
    [Token("Op", "@", _), ..rest] -> {
      let p1 = #(rest, 0, fn_, errors)
      let #(names, p2) = parse_binding_names(p1, [])
      // Expect . after the names
      let p3 = skip(".", p2)
      #(list.reverse(names), p3)
    }
    _ -> #([], p)
  }
}

/// Parse space-separated binding names until `.` or end.
fn parse_binding_names(p: Parser, acc: List(String)) -> #(List(String), Parser) {
  let #(tokens, pos, fn_, errors) = p
  case list.drop(tokens, pos) {
    [Token("Punct", ".", _), ..] -> #(acc, p)
    [Token("Name", v, _), ..rest] -> {
      let p1 = #(rest, 0, fn_, errors)
      parse_binding_names(p1, [v, ..acc])
    }
    _ -> #(acc, p)
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
fn parse_ctr(p: Parser, span: Span) -> #(NamedTerm, Parser) {
  let p1 = skip("#", p)
  let #(name, p2) = expect_name_opt(p1)
  case name {
    "" -> {
      let e = NamedErr("expected constructor name after #", span)
      #(e, p1)
    }
    _ -> {
      let #(tokens, pos, fn_, errors) = p2
      case list.drop(tokens, pos) {
        [Token("Punct", "(", _), ..rest] -> {
          let p3 = #(rest, 0, fn_, errors)
          let #(arg, p4) = parse_ctr_args(p3)
          let p5 = skip(")", p4)
          let arg_span = case arg {
            NamedRcd(_, s) -> s
            _ -> span
          }
          let final_span = merge(span, arg_span)
          #(NamedCtr(name, arg, final_span), p5)
        }
        _ -> {
          #(NamedCtr(name, NamedRcd([], span), span), p2)
        }
      }
    }
  }
}

/// Parse comma-separated constructor arguments inside #Name(...).
/// Returns a single argument directly, or a NamedRcd if there are multiple args.
fn parse_ctr_args(p: Parser) -> #(NamedTerm, Parser) {
  let #(tokens, pos, fn_, errors) = p
  let span = current_span(p)
  case list.drop(tokens, pos) {
    [Token("Punct", ")", _), ..] ->
      #(NamedRcd([], span), p)
    _ -> {
      let #(first, p1) = parse_term(p)
      // Check if next token is ',' (multiple args) or ')' (single arg)
      let #(tokens1, pos1, fn1, errors1) = p1
      case list.drop(tokens1, pos1) {
        [Token("Punct", ",", _), ..rest] -> {
          // Multiple arguments - wrap in NamedRcd
          let p2 = #(rest, 0, fn1, errors1)
          let #(next, p3) = parse_term(p2)
          let final_span = merge(span, term_span_named(next))
          #(NamedRcd([#("", first), #("", next)], final_span), p3)
        }
        _ ->
          // Single argument - return directly (don't wrap in NamedRcd)
          #(first, p1)
      }
    }
  }
}

// Record: {x: 1, y: 2}
fn parse_rcd(p: Parser, span: Span) -> #(NamedTerm, Parser) {
  let p1 = skip("{", p)
  let #(fields, p2) = parse_rcd_fields(p1, [])
  let p3 = skip("}", p2)
  #(NamedRcd(fields, span), p3)
}

fn parse_rcd_fields(
  p: Parser,
  acc: List(#(String, NamedTerm)),
) -> #(List(#(String, NamedTerm)), Parser) {
  let #(tokens, pos, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> {
      let err =
        ParseError(
          span: current_span(p),
          expected: "field",
          got: "EOF",
          context: "in record",
          rule: "parse_rcd_fields",
          surrounding: surrounding_tokens(tokens, pos),
        )
      #(list.reverse(acc), #(tokens, pos, fn_, [err, ..errors]))
    }
    [Token("Punct", "}", _), ..rest] -> #(
      list.reverse(acc),
      #(rest, 0, fn_, errors),
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

/// Parse record type fields: ${name: type = default?, name: type, ...}
/// Returns List(#(name, type, Option(default)))
fn parse_rcd_type_fields(
  p: Parser,
  acc: List(#(String, NamedTerm, Option(NamedTerm))),
) -> #(List(#(String, NamedTerm, Option(NamedTerm))), Parser) {
  let #(tokens, pos, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> {
      let err =
        ParseError(
          span: current_span(p),
          expected: "field",
          got: "EOF",
          context: "in record type",
          rule: "parse_rcd_type_fields",
          surrounding: surrounding_tokens(tokens, pos),
        )
      #(list.reverse(acc), #(tokens, pos, fn_, [err, ..errors]))
    }
    [Token("Punct", "}", _), ..rest] -> #(
      list.reverse(acc),
      #(rest, 0, fn_, errors),
    )
    [Token("Eof", ..), ..] -> #(list.reverse(acc), p)
    _ -> {
      let #(name, p2) = expect_name_opt(p)
      let p3 = skip(":", p2)
      let #(type_, p4) = parse_term(p3)
      // Check for optional default: = default
      let #(tokens2, pos2, fn2, err2) = p4
      let #(default_val, p5) = case list.drop(tokens2, pos2) {
        [Token("Punct", "=", _), Token("Punct", "}", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Punct", ";", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "=", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", ",", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", ")", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "]", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", ">", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "<", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Eof", ..), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "|", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "&", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "~", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "-", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", ":", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "@", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "^", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "!", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "#", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Op", "$", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Punct", "(", _), ..] ->
          #(
            None,
            #(tokens2, pos2, fn2, err2),
          )
        [Token("Punct", "=", _), Token("Name", ..), ..] -> {
          let p_eq = #(list.drop(tokens2, pos2 + 1), 0, fn2, err2)
          let #(default_, p_eq2) = parse_term(p_eq)
            #(Some(default_), p_eq2)
        }
        [Token("Punct", "=", _), Token("Integer", ..), ..] -> {
          let p_eq = #(list.drop(tokens2, pos2 + 1), 0, fn2, err2)
          let #(default_, p_eq2) = parse_term(p_eq)
            #(Some(default_), p_eq2)
        }
        [Token("Punct", "=", _), Token("Float", ..), ..] -> {
          let p_eq = #(list.drop(tokens2, pos2 + 1), 0, fn2, err2)
          let #(default_, p_eq2) = parse_term(p_eq)
            #(Some(default_), p_eq2)
        }
        _ -> #(
          None,
          #(tokens2, pos2, fn2, err2),
        )
      }
      let p6 = skip(",", p5)
      parse_rcd_type_fields(p6, [#(name, type_, default_val), ..acc])
    }
  }
}

fn parse_var(p: Parser, name: String, span: Span) -> #(NamedTerm, Parser) {
  case is_keyword(name) {
    True -> {
      let e = NamedErr("unexpected keyword: " <> name, span)
      #(e, p)
    }
    False -> {
      let #(tokens, pos, fn_, errors) = p
      #(NamedVar(name, span), #(tokens, pos, fn_, errors))
    }
  }
}

// Pi type: $pi(name: Domain) -> Codomain or $pi<a: Type>(a) -> a
fn parse_pi(p: Parser, span: Span) -> #(NamedTerm, Parser) {
  // Check for implicit params: <name: Type, ...>
  let #(implicits, p1) = case p {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Op", "<", _), ..] -> {
          let p2 = skip("<", p)
          let #(is, p3) = parse_implicit_params(p2)
          let p4 = skip(">", p3)
          #(is, p4)
        }
        _ -> #([], p)
      }
  }
  // Parse (name: Domain) or (name) or (Domain)
  let p2 = skip("(", p1)
  let #(name, p3) = expect_name_opt(p2)
  // Check for `: Domain` annotation
  let p4 = case p3 {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Punct", ":", _), ..] -> skip(":", p3)
        _ -> p3
      }
  }
  // Parse domain type
  let #(domain_type, p5) = case p4 {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Punct", ")", _), ..] -> {
          let term_span = merge(span, current_span(p4))
          #(case name {
              "" -> NamedVar("self", term_span)
              _ -> NamedVar(name, term_span)
            }, p4)
        }
        _ -> parse_term(p4)
      }
  }
  let p6 = skip(")", p5)
  // Check for `-> Codomain`
  let p_arrow = skip("->", p6)
  let #(codomain, p7) = case p_arrow {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [] -> #(NamedRcd([], span), p_arrow)
        _ -> {
          let #(ct, p2) = parse_term(p_arrow)
          #(ct, p2)
        }
      }
  }
  let final_span = merge(span, term_span_named(codomain))
  #(NamedPi(implicits, #(name, domain_type), codomain, final_span), p7)
}

// Lambda: $fn(name: Type) => body or $fn<a: Type>(name: Type) => body
fn parse_lambda(p: Parser, span: Span) -> #(NamedTerm, Parser) {
  // Check for implicit params: <name: Type, ...>
  let #(implicits, p1) = case p {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Op", "<", _), ..] -> {
          let p2 = skip("<", p)
          let #(is, p3) = parse_implicit_params(p2)
          let p4 = skip(">", p3)
          #(is, p4)
        }
        _ -> #([], p)
      }
  }
  // Parse (param: Type) => body
  let p2 = skip("(", p1)
  let #(name, p3) = expect_name_opt(p2)
  let p4 = case p3 {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Punct", ":", _), ..] -> skip(":", p3)
        _ -> p3
      }
  }
  let #(param_type, p5) = case p4 {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Punct", ")", _), ..] -> #(NamedHole(-1, span), p4) // uninstantiated hole
        _ -> parse_term(p4)
      }
  }
  let p6 = skip(")", p5)
  let p7 = skip("=>", p6)
  let #(body, rest) = parse_app(p7, merge(span, current_span(p7)))
  let final_span = merge(span, term_span_named(body))
  #(NamedLam(implicits, #(name, param_type), body, final_span), rest)
}

/// Parse implicit parameters: name: Type, name: Type, ...
fn parse_implicit_params(p: Parser) -> #(List(#(String, NamedTerm)), Parser) {
  parse_implicit_params_acc(p, [])
}

fn parse_implicit_params_acc(p: Parser, acc: List(#(String, NamedTerm))) -> #(List(#(String, NamedTerm)), Parser) {
  let #(name, p1) = expect_name_opt(p)
  case name {
    "" -> #(list.reverse(acc), p)
    _ -> {
      let p2 = skip(":", p1)
      let #(type_, p3) = parse_term(p2)
      let p4 = case p3 {
        #(tokens, pos, _, _) ->
          case list.drop(tokens, pos) {
            [Token("Punct", ",", _), ..] -> skip(",", p3)
            _ -> p3
          }
      }
      parse_implicit_params_acc(p4, [ #(name, type_), ..acc ])
    }
  }
}

// Match: $match (arg) { | pattern => body } or match (arg) { | pattern => body }
// Parentheses are required around the match argument to avoid ambiguity
// with record applications (e.g., $match n {..} would look like n applied to a record)
fn parse_match(p: Parser, span: Span) -> #(NamedTerm, Parser) {
  let p1 = case p {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Op", "$", _), ..] -> skip("$", p)
        _ -> p
      }
  }
  let p2 = skip("match", p1)
  // Require parentheses around the match argument
  let p3 = skip("(", p2)
  let #(arg, p4) = parse_term(p3)
  let p5 = skip(")", p4)
  // Optionally consume : Type or {type} annotation after the match argument
  // p5 is a Parser (tuple of 3 elements), check if next token is :
  let p6 = case p5 {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Punct", ":", _), ..] -> {
          let p_annot = skip(":", p5)
          let #(ann_type, p_new) = parse_term(p_annot)
          #(NamedAnn(arg, ann_type, current_span(p_annot)), p_new)
        }
        // Handle {type} annotation (without colon) when NOT followed by { | ... }
        // If followed by { | ... }, it's a match body, not a type annotation
        [Token("Punct", "{", _), Token("Punct", "|", _), ..rest] -> {
          // This is a match body, not a type annotation
          #(arg, p5)
        }
        [Token("Punct", "{", _), ..rest] -> {
          // Check if this is a type annotation by looking ahead for "|" after closing "}"
          let #(ann_type, p_after_annot) = parse_term(p5)
          case p_after_annot {
            #(tokens2, pos2, _, _) ->
              case list.drop(tokens2, pos2) {
                [Token("Punct", "{", _), Token("Punct", "|", _), ..] -> {
                  #(NamedAnn(arg, ann_type, current_span(p5)), p_after_annot)
                }
                _ -> #(arg, p5)
              }
          }
        }
        _ -> #(arg, p5)
      }
  }
  // p6 is now #(NamedTerm, Parser), extract the parser part
  let #(_, p7) = p6
  let p8 = skip("{", p7)
  let p9 = parse_cases(p8)
  let #(cases, rest) = p9
  let p10 = skip("}", rest)
  let final_span = merge(span, case_list_span_named(cases, span))
  #(NamedMatch(arg, cases, final_span), p10)
}

fn parse_cases(p: Parser) -> #(List(NamedCase), Parser) {
  let #(cases, p1) = parse_cases_acc(p, [])
  #(list.reverse(cases), p1)
}

fn parse_cases_acc(p: Parser, acc: List(NamedCase)) -> #(List(NamedCase), Parser) {
  let span = current_span(p)
  let #(tokens, pos, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> {
      let err =
        ParseError(
          span: current_span(p),
          expected: "case pattern",
          got: "EOF",
          context: "end of match",
          rule: "parse_cases_acc",
          surrounding: surrounding_tokens(tokens, pos),
        )
      #(acc, #(tokens, pos, fn_, [err, ..errors]))
    }
    [Token("Punct", "}", _), ..rest] -> #(
      acc,
      #(rest, 0, fn_, errors),
    )
    [Token("Eof", ..), ..] -> #(acc, p)
    _ -> {
      let p1 = skip("|", p)
      // Guard: if skip("|") didn't advance, we're not at a valid case.
      // Return accumulated cases to avoid infinite loop.
      case p1 {
        #(_, pos1, _, _) ->
          case pos1 == pos {
            True -> #(acc, p1)
            False -> {
              let #(pattern, p2) = parse_pattern(p1)
              let #(guard, p3) = case p2 {
                #(tokens2, pos2, fn2, errors2) ->
                  case list.drop(tokens2, pos2) {
                    [Token("Op", "?", _), ..] -> {
                      let p = #(tokens2, pos2 + 1, fn2, errors2)
                      let #(g, p4) = parse_term(p)
                      #(Some(g), p4)
                    }
                    _ -> #(None, p2)
                  }
              }
              let p5 = skip("=>", p3)
              let #(body, p6) = parse_term(p5)
              // Optionally consume -> ReturnType annotation (just an annotation, doesn't affect semantics)
              let p7 = case p6 {
                #(tokens, pos, fn_, errors) ->
                  case list.drop(tokens, pos) {
                    [Token("Op", "-", _), Token("Op", ">", _), ..rest] -> {
                      let p_after = #(rest, pos + 2, fn_, errors)
                      let #(ret_type, p8) = parse_term(p_after)
                      #(NamedAnn(body, ret_type, current_span(p_after)), p8)
                    }
                    _ -> #(body, p6)
                  }
              }
              let case_term = NC(pattern, None, p7.0, span)
              parse_cases_acc(p7.1, [case_term, ..acc])
            }
          }
      }
    }
  }
}

// Let: $let name = value; body — desugars to App(Lam(name, _, body), value)
fn parse_let(p: Parser, span: Span) -> #(NamedTerm, Parser) {
  let p1 = skip("let", p)
  let #(name, p2) = expect_name_opt(p1)
  // Check for optional type annotation
  let p3 = case p2 {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Punct", ":", _), ..] -> skip(":", p2)
        _ -> p2
      }
  }
  // Parse optional type or use Rcd as default
  let #(param_type, p4) = case p3 {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        // Handle $Int, $Float, $Type, etc.
        [Token("Op", "$", _), Token("Name", _, _), ..] -> parse_term(p3)
        // Handle ${...} record type syntax
        [Token("Op", "$", _), Token("Punct", "{", _), ..] -> parse_term(p3)
        // Handle {field: type, ...} record type (without $)
        [Token("Punct", "{", _), ..] -> parse_term(p3)
        _ -> #(NamedRcd([], span), p3)
      }
  }
  let p5 = skip("=", p4)
  let #(value, rest) = parse_term(p5)
  let let_span = merge(span, term_span_named(value))
  // Check for semicolon as separator (newlines are optional)
  let p6 = case rest {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Punct", ";", _), ..] -> skip(";", rest)
        _ -> rest
      }
  }
  // Check if there's a body expression (not Eof or empty)
  let #(body, rest_final) = case p6 {
    #(tokens, pos, _, _) ->
      case list.drop(tokens, pos) {
        [Token("Eof", ..), ..] -> #(value, p6)
        [] -> #(value, p6)
        _ -> parse_app(p6, let_span)
      }
  }
  let body_span = merge(let_span, term_span_named(body))
  #(NamedLet(name, param_type, value, body, body_span), rest_final)
}

// Fix: $fix name. body — the body contains the recursive reference as a named variable
// The term_to_debruijn pass handles converting the fix variable to the correct De Bruijn index.
fn parse_fix(p: Parser, span: Span) -> #(NamedTerm, Parser) {
  let p1 = skip("fix", p)
  let #(name, p2) = expect_name_opt(p1)
  // Expect '.' separator after the fix variable name.
  // If '=' is present, emit a syntax error but continue parsing.
  let p3 = case p2 {
    #(tokens, pos, fn_, errors) ->
      case list.drop(tokens, pos) {
        [Token("Punct", ".", _), ..rest] ->
          #(rest, 0, fn_, errors)
        [Token("Punct", "=", _), Token("Op", ">", _), .._] -> {
          let err = ParseError(
            span: current_span(p2),
            expected: ".",
            got: "=>",
            context: "fix expression",
            rule: "parse_fix",
            surrounding: surrounding_tokens(tokens, pos),
          )
          #(tokens, pos, fn_, [err, ..errors])
        }
        [Token("Punct", "=", _), .._] -> {
          let err = ParseError(
            span: current_span(p2),
            expected: ".",
            got: "=",
            context: "fix expression",
            rule: "parse_fix",
            surrounding: surrounding_tokens(tokens, pos),
          )
          #(tokens, pos, fn_, [err, ..errors])
        }
        _ -> {
          let got = case list.drop(tokens, pos) {
            [Token(k, v, _), ..] -> k <> " '" <> v <> "'"
            [] -> "end of input"
          }
          let err = ParseError(
            span: current_span(p2),
            expected: ".",
            got: got,
            context: "fix expression",
            rule: "parse_fix",
            surrounding: surrounding_tokens(tokens, pos),
          )
          #(tokens, pos, fn_, [err, ..errors])
        }
      }
  }
  // Parse the value expression (the lambda). No separate body parsing —
  // any trailing expressions are handled by the outer $let.
  let #(body, rest) = parse_term(p3)
  let final_span = merge(span, term_span_named(body))
  #(NamedFix(name, body, final_span), rest)
}

// If: if cond then body else else_body
// List: [1, 2, 3]
fn parse_list(p: Parser, span: Span) -> #(NamedTerm, Parser) {
  let #(items, p1) = parse_list_items(p)
  let p2 = skip("]", p1)
  let fields = list.index_map(items, fn(item, i) { #(int.to_string(i), item) })
  let result = NamedRcd(fields, span)
  #(result, p2)
}

fn parse_list_items(p: Parser) -> #(List(NamedTerm), Parser) {
  parse_list_items_acc(p, [])
}

fn parse_list_items_acc(p: Parser, acc: List(NamedTerm)) -> #(List(NamedTerm), Parser) {
  let #(tokens, pos, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> {
      let err =
        ParseError(
          span: current_span(p),
          expected: "list item",
          got: "EOF",
          context: "in list",
          rule: "parse_list_items_acc",
          surrounding: surrounding_tokens(tokens, pos),
        )
      #(list.reverse(acc), #(tokens, pos, fn_, [err, ..errors]))
    }
    [Token("Punct", "]", _), ..rest] -> #(
      list.reverse(acc),
      #(rest, 0, fn_, errors),
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
  let #(tokens, pos, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> #(PAny(span), p)
    [Token("Name", "_", _), ..] -> #(
      PAny(span),
      #(tokens, pos + 1, fn_, errors),
    )
    [Token("Op", "#", _), .._] -> {
      let p1 = #(tokens, pos + 1, fn_, errors)
      let #(name, _) = expect_name_opt(p1)
      case name {
        "" -> #(PAny(span), p1)
        _ ->
          case list.drop(tokens, pos) {
            [Token("Op", "#", _), Token("Name", v, _), Token("Punct", "(", _), ..inner_rest] -> {
              let p3 = #(inner_rest, 0, fn_, errors)
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
      let p1 = #(tokens, pos + 1, fn_, errors)
      case rest {
        [] -> {
          #(PVar(v, span), p1)
        }
        [Token("Op", "@", _), ..inner_rest] -> {
          let p2 = #(inner_rest, 0, fn_, errors)
          let #(inner, p3) = parse_pattern(p2)
          let final_span = merge(span, current_span(p3))
          #(PAlias(v, inner, final_span), p3)
        }
        [Token("Punct", "(", _), ..inner_rest] -> {
          let p2 = #(inner_rest, 0, fn_, errors)
          let #(inner, p3) = parse_pattern(p2)
          let p4 = skip(")", p3)
          let final_span = merge(span, current_span(p4))
          #(PCtr(v, inner, final_span), p4)
        }
        _ -> {
          #(PVar(v, span), p1)
        }
      }
    }
    [Token("Punct", "(", _), Token("Punct", ")", _), ..] -> {
      let p1 = #(tokens, pos + 2, fn_, errors)
      #(PUnit(span), p1)
    }
    [Token("Integer", v, _), ..] -> {
      let p1 = #(tokens, pos + 1, fn_, errors)
      case int.parse(v) {
        Ok(value) -> #(PLit(LitInt(value), span), p1)
        Error(_) -> {
          let err =
            ParseError(
              span: span,
              expected: "integer",
              got: v,
              context: "invalid integer literal",
              rule: "parse_pattern",
              surrounding: surrounding_tokens(tokens, pos),
            )
          #(PAny(span), #(tokens, pos + 1, fn_, [err, ..errors]))
        }
      }
    }
    [Token("Float", v, _), ..] -> {
      let p1 = #(tokens, pos + 1, fn_, errors)
      case float.parse(v) {
        Ok(value) -> #(PLit(LitFloat(value), span), p1)
        Error(_) -> {
          let err =
            ParseError(
              span: span,
              expected: "float",
              got: v,
              context: "invalid float literal",
              rule: "parse_pattern",
              surrounding: surrounding_tokens(tokens, pos),
            )
          #(PAny(span), #(tokens, pos + 1, fn_, [err, ..errors]))
        }
      }
    }
    // Error pattern: $error
    [Token("Op", "$", _), Token("Name", "error", _), ..rest] ->
      #(PError(span), #(rest, 0, fn_, errors))
    // Type patterns: $Type with optional <T> params, or literal types
    [Token("Op", "$", _), Token("Name", name, _), ..rest] -> {
      case name {
        "Type" -> {
          // Check for optional <T> type parameters
          case rest {
            [Token("Op", "<", _), Token("Integer", v, _), Token("Op", ">", _), ..rest2] -> {
              let lvl = case int.parse(v) {
                Ok(n) -> n
                Error(_) -> 0
              }
              let p1 = #(rest2, 0, fn_, errors)
              #(PTyp(lvl, span), p1)
            }
            [Token("Op", "<", _), Token("Name", v, _), Token("Op", ">", _), ..rest2] -> {
              let lvl = case int.parse(v) {
                Ok(n) -> n
                Error(_) -> 0
              }
              let p1 = #(rest2, 0, fn_, errors)
              #(PTyp(lvl, span), p1)
            }
            _ -> {
              #(PTyp(0, span), #(rest, 0, fn_, errors))
            }
          }
        }
        "Int" -> {
          let p1 = #(rest, 0, fn_, errors)
          #(PLitT(IntT, span), p1)
        }
        "Float" -> {
          let p1 = #(rest, 0, fn_, errors)
          #(PLitT(FloatT, span), p1)
        }
        "I8" | "I16" | "I32" | "I64" |
        "U8" | "U16" | "U32" | "U64" |
        "F16" | "F32" | "F64" -> {
          let p1 = #(rest, 0, fn_, errors)
          #(PAny(span), p1)
        }
        _ -> {
          let p1 = #(rest, 0, fn_, errors)
          #(PAny(span), p1)
        }
      }
    }
    // Type record pattern: ${field: type, ...}
    [Token("Op", "$", _), Token("Punct", "{", _), ..rest] -> {
      let p1 = #(rest, 0, fn_, errors)
      let #(fields, p2) = parse_pattern_fields(p1)
      let p3 = skip("}", p2)
      let final_span = merge(span, current_span(p3))
      #(PRcd(fields, final_span), p3)
    }
    // Record pattern: {field: pattern, ...}
    [Token("Punct", "{", _), ..rest] -> {
      let p1 = #(rest, 0, fn_, errors)
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
  let #(tokens, pos, fn_, errors) = p
  case list.drop(tokens, pos) {
    [] -> #(list.reverse(acc), p)
    [Token("Punct", "}", _), ..rest] -> #(
      list.reverse(acc),
      #(rest, 0, fn_, errors),
    )
    _ -> {
      let #(name, p2) = expect_name_opt(p)
      case name {
        "" -> {
          #(list.reverse(acc), p)
        }
        v -> {
          let p3 = case p2 {
            #(tokens, pos, _, _) ->
              case list.drop(tokens, pos) {
                [Token("Punct", ":", _), ..] -> skip(":", p2)
                _ -> p2
              }
          }
          let current = current_span(p3)
          let #(inner, p4) = case p3 {
            #(tokens, pos, _, _) ->
              case list.drop(tokens, pos) {
                [Token("Punct", "}", _), ..] -> {
                  #(PVar(v, current), p3)
                }
                [Token("Punct", ",", _), ..] -> {
                  #(PVar(v, current), skip(",", p3))
                }
                _ -> {
                  let #(pat, p) = parse_pattern(p3)
                  #(pat, p)
                }
              }
          }
          let p5 = skip("}", p4)
          let p6 = case p5 {
            #(tokens, pos, _, _) ->
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

fn case_list_span_named(cases: List(NamedCase), default: Span) -> Span {
  case cases {
    [] -> default
    [NC(_, _, body, _), ..] -> merge(default, term_span_named(body))
  }
}

fn is_keyword(s: String) -> Bool {
  case s {
    "fun" | "let" | "match" | "fix" | "type" | "hole" | "unit" | "true" | "false" -> True
    _ -> False
  }
}
