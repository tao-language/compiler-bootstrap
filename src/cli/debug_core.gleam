/// Debug Core CLI Command — Inspect the full compiler pipeline
///
/// Usage: gleam run debug-core "expression"
///
/// This command takes a Core expression string and runs the entire
/// pipeline (tokenize → parse → infer → evaluate), printing structured
/// debug information at each stage.
///
/// ## Output Format
///
/// - **STDOUT**: Structured debug sections separated by blank lines
/// - **STDERR**: Error messages from parsing or type checking
///
/// Sections printed to stdout:
/// 1. SOURCE — The input expression
/// 2. TOKENS — Tokenized representation
/// 3. PARSING — The parsed Term
/// 4. PARSE_ERRORS — Any parse errors (empty if none)
/// 5. DEBRUIJN — The de Bruijn-converted Term (via term_to_debruijn)
/// 6. INFERENCE — Inferred value, type, and final state
/// 7. EVALUATION — Evaluated result value
/// 8. ERRORS — Type checking errors (empty if none)

import gleam/io
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import core/ast.{
  type Term, type Value,
  type Case, type Pattern,
  VErr, VCtr, VRcd, VLit, VLam, VNeut, VPi, VTyp,
  Lit, Var, App, Lam, Pi, Match, Ann, Call, Rcd, RcdT, Typ, TypeDef,
  LitT, Ctr, Fix, Err, Hole,
  Int as LitInt, Float as LitFloat,
  term_to_string,
}
import core/infer.{infer}
import core/eval.{evaluate, do_app, eval_value_to_string}
import core/state.{initial_state, type Error, error_to_string, type FfiEntry, FfiEntry, type State}
import core/syntax.{parse}
import syntax/base_lexer.{tokenize, type Token, Token as TokenCtor}
import syntax/grammar.{type ParseError}

/// Run the debug-core command with the given expression string.
///
/// This is the main entry point for the debug-core CLI command.
/// It runs the full pipeline and prints structured debug output.
pub fn run(expression: String) -> Nil {
  // Print source section
  io.println("=== SOURCE ===")
  io.println(expression <> "\n")

  // Step 1: Tokenize
  let tokens = tokenize(expression)
  io.println("=== TOKENS ===")
  io.println(format_tokens(tokens))

  // Step 2: Parse (returns Term with de Bruijn indices directly)
  let #(term, parse_errors) = parse(expression)

  io.println("\n=== PARSING ===")
  io.println(term_to_string(term))

  // Step 3: Show parse errors
  case parse_errors {
    [] -> io.println("\n  (no parse errors)")
    errs -> {
      io.println("\n=== PARSE ERRORS ===")
      list.each(errs, fn(e) {
        io.println("  " <> format_parse_error(e))
      })
    }
  }

  // Step 4: Show de Bruijn representation (parser already produces de Bruijn terms)
  io.println("\n=== DEBRUIJN ===")
  io.println(term_to_string(term))

  // Step 5: Type inference
  let state = initial_state(ffi_entries())
  let #(value, inferred_type, final_state) = infer(state, term)

  io.println("\n=== INFERENCE ===")
  io.println("  Value: " <> eval_value_to_string(value))
  io.println("  Type:  " <> eval_value_to_string(inferred_type))
  io.println("  Errors: " <> int.to_string(list.length(final_state.errors)))

  // Step 6: Evaluate (normalize) with FFI
  let eval_result = evaluate(initial_state(ffi_entries()), term)
  io.println("\n=== EVALUATION ===")
  io.println("  Result: " <> eval_value_to_string(eval_result))

  // Step 7: Show type errors
  case final_state.errors {
    [] -> {
      io.println("\n=== ERRORS ===")
      io.println("  (none)")
    }
    errs -> {
      io.println("\n=== ERRORS ===")
      list.each(errs, fn(e) {
        io.println("  " <> format_error(e))
      })
    }
  }
}

// ============================================================================
// FORMATTING HELPERS
// ============================================================================

fn format_tokens(tokens: List(Token)) -> String {
  list.map(tokens, fn(t) {
    case t {
      TokenCtor(kind: kind, value: value, span: span) ->
        "Token(" <> kind <> ", " <> value <> ", "
        <> int.to_string(span.start_line) <> ":" <> int.to_string(span.start_col) <> ")"
    }
  }) |> string.join("\n")
}

fn format_parse_error(err: ParseError) -> String {
  let line_col = int.to_string(err.span.start_line) <> ":"
  <> int.to_string(err.span.start_col)
  let rule_info = case err.rule {
    "" -> ""
    rule -> " (rule: " <> rule <> ")"
  }
  let surrounding_info = case err.surrounding {
    [] -> ""
    tokens ->
      "\n  surrounding: " <> token_list(tokens)
  }
  "  " <> line_col <> " expected " <> err.expected <> ", got " <> err.got
  <> rule_info <> surrounding_info
}

/// Format surrounding tokens for error reporting.
fn token_list(tokens: List(Token)) -> String {
  case tokens {
    [] -> ""
    [first, ..rest] -> case rest {
      [] -> token_to_string(first)
      _ -> token_to_string(first) <> " " <> string.join(list.map(rest, token_to_string), with: " ")
    }
  }
}

/// Format a token to a human-readable string.
fn token_to_string(tok: Token) -> String {
  case tok {
    TokenCtor(kind: kind, value: value, span: _) ->
      case kind {
        "Name" -> "Name '" <> value <> "'"
        "Op" -> "Op '" <> value <> "'"
        "Punct" -> "Punct '" <> value <> "'"
        "Integer" -> "Integer '" <> value <> "'"
        "Float" -> "Float '" <> value <> "'"
        "String" -> "String '" <> value <> "'"
        "Eof" -> "EOF"
        "Keyword" -> "Keyword '" <> value <> "'"
        _ -> value
      }
  }
}

/// Format a parse error with full context including surrounding tokens.
fn format_parse_error_verbose(err: ParseError) -> String {
  let line_col = int.to_string(err.span.start_line) <> ":"
  <> int.to_string(err.span.start_col)
  let rule_info = case err.rule {
    "" -> ""
    rule -> "\n  rule: " <> rule
  }
  let context_info = case err.context {
    "" -> ""
    ctx -> "\n  context: " <> ctx
  }
  let surrounding_info = case err.surrounding {
    [] -> ""
    tokens ->
      "\n  surrounding: " <> token_list(tokens)
  }
  "Parse error at " <> line_col <> "\n"
  <> "  expected: " <> err.expected <> "\n"
  <> "  got: " <> err.got <> rule_info <> context_info <> surrounding_info
}

fn format_error(err: Error) -> String {
  error_to_string(err)
}

// ============================================================================
// DEBUG EVALUATION TRACING
// ============================================================================

/// Format a term short for debug output.
fn term_short(term: Term) -> String {
  case term {
    Var(i, _) -> "Var(" <> int.to_string(i) <> ")"
    App(fun, arg, _) -> "App(" <> term_short(fun) <> ", " <> term_short(arg) <> ")"
    Lam(_, #(name, _), _, _) -> "Lam(" <> name <> ")"
    _ -> term_to_string(term)
  }
}

/// Recursively evaluate and print each App step.
fn debug_eval(state: State, term: Term, depth: Int) -> Value {
  let indent = string.repeat("  ", depth)
  io.println(indent <> "EVAL: " <> term_short(term))
  
  case term {
    App(fun, arg, _) -> {
      let fun_val = evaluate(state, fun)
      io.println(indent <> "  fun => " <> eval_value_to_string(fun_val))
      let arg_val = evaluate(state, arg)
      io.println(indent <> "  arg => " <> eval_value_to_string(arg_val))
      let result = do_app(state, fun_val, arg_val)
      io.println(indent <> "  => " <> eval_value_to_string(result))
      result
    }
    _ -> evaluate(state, term)
  }
}

/// Minimal FFI stubs for debug-core
fn ffi_entries() -> List(FfiEntry) {
  [
    FfiEntry("i32_add", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(LitInt(a)), _), #(VLit(LitInt(b)), _), ..] -> Some(VLit(LitInt(a + b)))
        _ -> None
      }
    }),
    FfiEntry("i32_sub", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(LitInt(a)), _), #(VLit(LitInt(b)), _), ..] -> Some(VLit(LitInt(a - b)))
        _ -> None
      }
    }),
    FfiEntry("i32_mul", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(LitInt(a)), _), #(VLit(LitInt(b)), _), ..] -> Some(VLit(LitInt(a * b)))
        _ -> None
      }
    }),
    FfiEntry("i32_eq", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(LitInt(a)), _), #(VLit(LitInt(b)), _), ..] ->
          case a == b {
            True -> Some(VCtr("True", VRcd([])))
            False -> Some(VCtr("False", VRcd([])))
          }
        _ -> None
      }
    }),
  ]
}
