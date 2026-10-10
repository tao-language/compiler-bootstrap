/// `tao debug-parse` — lex and parse Tao source and print everything a parser
/// developer needs to see what went wrong:
///
///   source   the input (inline, or read from a file)
///   lex      the full token stream, with each token's position, lexeme and
///            constructor
///   parse    the outcome: on success the AST; on failure *every* dead end
///            (position, problem, context) sorted furthest-first, plus the
///            single "best" error the user would actually see
///
/// Unlike `debug-expr`/`debug-file` (which run the whole Tao → Core pipeline),
/// this stops at the parser — it is the tool for "why did this not parse?".
import core/error
import gleam/int
import gleam/io
import gleam/list
import gleam/order
import gleam/string
import nibble
import nibble/lexer.{type Span as NibbleSpan}
import tao/parse.{
  type Token, dead_ends_to_error, parse_expression, parse_statements, tokens,
  Parsed, ParseFailed,
}

/// Render the full lex + parse outcome of `source`, labelled `file_label`
/// (a path when read from a file, `<debug-parse>` when inline). When
/// `as_expr` is True the source is parsed as a single expression, otherwise
/// as a whole module.
pub fn debug_parse(file_label: String, source: String, as_expr: Bool) -> Nil {
  io.println(">> source (" <> file_label <> ")")
  io.println(source)
  io.println("")

  io.println(">> lex -> tokens")
  case tokens(file_label, source) {
    Error(err) -> {
      io.println_error("❌ " <> error.display_syntax(err))
      io.println("")
      exit(1)
    }
    Ok(toks) -> {
      io.println("// " <> int.to_string(list.length(toks)) <> " tokens")
      list.map(toks, fn(tok) {
        io.println(render_token(tok))
        Nil
      })
      Nil
    }
  }
  io.println("")

  case as_expr {
    True -> parse_and_print_expression(file_label, source)
    False -> parse_and_print_module(file_label, source)
  }
}

fn parse_and_print_expression(file: String, source: String) -> Nil {
  io.println(">> parse -> expression")
  case parse_expression(file, source) {
    Error(_) -> internal_lex_failure()
    Ok(Parsed(ast)) -> print_ok(ast)
    Ok(ParseFailed(dead_ends)) -> print_failed(file, dead_ends)
  }
}

fn parse_and_print_module(file: String, source: String) -> Nil {
  io.println(">> parse -> module")
  case parse_statements(file, source) {
    Error(_) -> internal_lex_failure()
    Ok(Parsed(stmts)) -> print_ok(stmts)
    Ok(ParseFailed(dead_ends)) -> print_failed(file, dead_ends)
  }
}

/// Print a successful parse: the AST via inspect.
fn print_ok(ast: a) -> Nil {
  io.println("OK")
  io.println(string.inspect(ast))
  io.println("")
}

/// Print every dead end (furthest first) and the single best error the user
/// would see, then exit non-zero.
fn print_failed(file: String, dead_ends: List(nibble.DeadEnd(Token, String))) {
  print_dead_ends(dead_ends)
  io.println("")
  io.println(">> best error (what the user sees)")
  let best = dead_ends_to_error(file, dead_ends)
  io.println("❌ " <> error.display_syntax(best))
  io.println("")
  exit(1)
}

fn internal_lex_failure() -> Nil {
  // Unreachable: a lex failure already exits in `debug_parse`.
  io.println_error("internal error: parse reported a lex failure")
  exit(1)
}

/// Render one token as `  <row>:<col>  "<lexeme>"  <constructor>`.
fn render_token(tok: lexer.Token(Token)) -> String {
  let span = tok.span
  let pos =
    int.to_string(span.row_start) <> ":" <> int.to_string(span.col_start)
  "  " <> pad(pos, 8) <> " \"" <> tok.lexeme <> "\"  "
  <> string.inspect(tok.value)
}

/// Render every dead end, sorted furthest-first (the most informative
/// failure first), each with its position, problem and context stack.
fn print_dead_ends(dead_ends: List(nibble.DeadEnd(Token, String))) {
  // Furthest first: `a` sorts before `b` when `a` is further along.
  let sorted =
    list.sort(dead_ends, fn(a, b) {
      case pos_after(a.pos, b.pos) {
        True -> order.Lt
        False ->
          case pos_after(b.pos, a.pos) {
            True -> order.Gt
            False -> order.Eq
          }
      }
    })
  io.println(
    "FAILED ("
      <> int.to_string(list.length(dead_ends))
      <> " dead ends, furthest first):",
  )
  let numbered = list.index_map(sorted, fn(de, i) { #(i + 1, de) })
  list.map(numbered, fn(pair) {
    let #(i, de) = pair
    let pos =
      int.to_string(de.pos.row_start) <> ":" <> int.to_string(de.pos.col_start)
    io.println(
      "  ["
        <> int.to_string(i)
        <> "] "
        <> pad(pos, 6)
        <> " "
        <> render_problem(de.problem)
        <> "   in: "
        <> render_context(de.context),
    )
    Nil
  })
}

/// Render a nibble parse problem, keeping token constructors (via inspect) so
/// a parser developer sees the exact tokens involved.
fn render_problem(problem: nibble.Error(Token)) -> String {
  case problem {
    nibble.Expected(expecting, got) ->
      "Expected(" <> expecting <> ", got=" <> string.inspect(got) <> ")"
    nibble.Unexpected(tok) -> "Unexpected(" <> string.inspect(tok) <> ")"
    nibble.EndOfInput -> "EndOfInput"
    nibble.Custom(message) -> "Custom(" <> message <> ")"
    nibble.BadParser(message) -> "BadParser(" <> message <> ")"
  }
}

/// Render the context stack (innermost first) as `a > b > c`.
fn render_context(context: List(#(NibbleSpan, String))) -> String {
  let labels = list.map(context, fn(entry) { entry.1 })
  case labels {
    [] -> "(top level)"
    _ -> string.join(labels, " > ")
  }
}

/// True when position `a` is strictly after position `b`.
fn pos_after(a: NibbleSpan, b: NibbleSpan) -> Bool {
  a.row_start > b.row_start
  || { a.row_start == b.row_start && a.col_start > b.col_start }
}

/// Left-pad `s` with spaces to a total width of `width`.
fn pad(s: String, width: Int) -> String {
  let padding = width - string.length(s)
  case padding > 0 {
    True -> string.repeat(" ", padding) <> s
    False -> s
  }
}

/// Terminate the process with `status`.
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil
