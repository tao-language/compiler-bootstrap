/// The single compile pipeline shared by the `check`/`run`/`test`
/// commands: input resolution, parsing (with `--trace parse`), package
/// loading, and declare/define/resolve with `--trace` observation at
/// each phase.
import cli/args.{type Input, type Opts, InputExpr, InputFiles, InputStmts}
import cli/common
import core/context.{
  type Context,
  type TraceKind,
  Context,
  TraceDefines,
  TraceHoles,
  TraceModules,
  TraceParse,
  new_ctx,
}
import core/error as e
import core/ffi
import core/format
import core/resolve
import core/value as v
import filepath
import gleam/int
import gleam/io
import gleam/list
import gleam/order
import gleam/option.{type Option, None, Some}
import gleam/string
import nibble
import nibble/lexer.{type Span as NibbleSpan}
import simplifile
import tao/ast.{type Module} as tao
import tao/config
import tao/declare
import tao/define
import tao/load
import tao/parse.{type Token as ParseToken}
import tao/trace

/// The name `-e` expressions are wrapped in (`let __result = <expr>`);
/// `run` prints its value bare (REPL-style).
pub const expr_result_name = "__result"

@external(erlang, "erlang", "system_time")
fn now_ns() -> Int

fn now() -> Int {
  now_ns() / 1_000_000
}

/// A pipeline failure: a loading problem (path expansion, file read) or
/// syntax (parse) errors. The pipeline does not print; the commands do.
pub type Failure {
  LoadFailure(String)
  SyntaxFailures(List(e.Error))
}

/// The result of `compile_input`: the input modules (packages excluded)
/// and the post-compile context.
pub type Compiled {
  Compiled(
    /// The expanded input paths, or the inline label (`<expr>`/`<stmt>`).
    paths: List(String),
    /// The input modules, in input order.
    modules: List(Module),
    /// The context after declare/define/resolve (with any errors).
    ctx: Context,
  )
}

/// Run the input through the whole pipeline (pure: no printing). The
/// prelude is always loaded; build errors, if any, are in `Compiled.ctx`.
pub fn compile_input(input: Input, opts: Opts) -> Result(Compiled, Failure) {
  case resolve_sources(input) {
    Error(msg) -> Error(LoadFailure(msg))
    Ok(sources) -> compile_sources(sources, opts)
  }
}

/// Resolve the input to (label, source) pairs: files are read from
/// disk; inline inputs are wrapped into an anonymous module body.
fn resolve_sources(input: Input) -> Result(List(#(String, String)), String) {
  case input {
    InputFiles(paths) ->
      case common.expand_paths(paths) {
        Error(msg) -> Error(msg)
        Ok(files) -> read_sources(files)
      }
    InputExpr(source) ->
      Ok([#("<expr>", "let " <> expr_result_name <> " = " <> source)])
    InputStmts(source) -> Ok([#("<stmt>", source)])
  }
}

fn read_sources(files: List(String)) -> Result(List(#(String, String)), String) {
  list.fold(files, Ok([]), fn(acc, file) {
    case acc, simplifile.read(file) {
      Error(_), _ -> acc
      Ok(sources), Ok(source) -> Ok(list.append(sources, [#(file, source)]))
      Ok(_), Error(err) ->
        Error("could not read " <> file <> ": " <> simplifile.describe_error(err))
    }
  })
}

fn compile_sources(
  sources: List(#(String, String)),
  opts: Opts,
) -> Result(Compiled, Failure) {
  let #(mods, errors) = parse_all(sources, opts.trace)
  case list.length(errors) {
    0 -> Ok(compile_mods(sources, mods, opts))
    _ -> Error(SyntaxFailures(errors))
  }
}

fn compile_mods(
  sources: List(#(String, String)),
  mods: List(Module),
  opts: Opts,
) -> Compiled {
  let paths = list.map(sources, fn(s) { s.0 })
  let packages = resolve_packages(opts.packages)
  let search_paths = case opts.paths {
    [] -> ["lib"]
    _ -> opts.paths
  }
  let #(mods, all) = load.project_modules(search_paths, mods, packages)
  let prelude = load.prelude_modules(all)
  let all = load.implicit_prelude_imports(all, prelude)

  let ctx = Context(
    ..new_ctx,
    ffi: ffi.build,
    trace_kinds: opts.trace,
    traced_mods: list.map(mods, fn(m) { m.0 }),
  )
  let #(defs, declare_errors) = declare.modules(all)
  let ctx = Context(..ctx, errors: list.append(declare_errors, ctx.errors))

  case list.contains(opts.trace, TraceModules) {
    True -> {
      let _ = trace.module_trace(all, defs)
      Nil
    }
    False -> Nil
  }
  case list.contains(opts.trace, TraceDefines) {
    True -> defines_listing(defs)
    False -> Nil
  }

  let t0 = now()
  let ctx = define.types(ctx, defs)
  let t1 = now()
  let ctx = define.values(ctx, defs)
  case list.contains(opts.trace, TraceDefines) {
    True -> {
      io.println(
        "// define.types: "
          <> int.to_string(t1 - t0)
          <> "ms holes="
          <> int.to_string(ctx.hole_counter),
      )
      io.println(
        "// define.values: "
          <> int.to_string(now() - t1)
          <> "ms holes="
          <> int.to_string(ctx.hole_counter),
      )
      Nil
    }
    False -> Nil
  }
  case list.contains(opts.trace, TraceHoles) {
    True -> holes_dump(ctx, "after define")
    False -> Nil
  }

  case opts.dump_def {
    Some(name) -> dump_def(ctx, mods, name)
    None -> Nil
  }

  // `--dump-def` stops before resolve, as `debug-src --dump-def` did.
  let ctx = case opts.dump_def {
    Some(_) -> ctx
    None -> {
      let t2 = now()
      let ctx = resolve.context(ctx)
      case list.contains(opts.trace, TraceDefines) {
        True ->
          io.println(
            "// resolve.context: " <> int.to_string(now() - t2) <> "ms",
          )
        False -> Nil
      }
      case list.contains(opts.trace, TraceHoles) {
        True -> holes_dump(ctx, "after resolve")
        False -> Nil
      }
      ctx
    }
  }

  Compiled(paths: paths, modules: mods, ctx: ctx)
}

/// The package list: the project's `tao.toml` deps (if a project root
/// exists) plus any `--add` packages, with the prelude always included.
fn resolve_packages(
  extra: List(#(String, Option(String))),
) -> List(#(String, Option(String))) {
  case config.find_project_root(".") {
    Some(root) -> {
      let manifest_path = filepath.join(root, "tao.toml")
      case config.load(manifest_path) {
        Ok(cfg) -> {
          let deps = list.map(cfg.dependencies, fn(d) { #(d.name, d.version) })
          load.with_prelude(list.append(deps, extra))
        }
        Error(_) -> load.with_prelude(extra)
      }
    }
    None -> load.with_prelude(extra)
  }
}

// ============================================================================
// --trace parse
// ============================================================================

/// Parse every source into a module. With `TraceParse`, prints the
/// token stream and the parse outcome (the AST, or *every* dead end plus
/// the single best error) for each source.
fn parse_all(
  sources: List(#(String, String)),
  trace: List(TraceKind),
) -> #(List(Module), List(e.Error)) {
  let show = list.contains(trace, TraceParse)
  list.fold(sources, #([], []), fn(acc, source) {
    let #(label, src) = source
    let #(mods, errors) = parse_one(label, src, show)
    #(list.append(acc.0, mods), list.append(acc.1, errors))
  })
}

fn parse_one(label: String, src: String, show: Bool) -> #(List(Module), List(e.Error)) {
  case show {
    False ->
      case parse.statements(label, src) {
        Ok(stmts) -> #([#(label, stmts)], [])
        Error(err) -> #([], [err])
      }
    True -> {
      io.println(">> source (" <> label <> ")")
      io.println(src)
      io.println("")
      io.println(">> lex -> tokens")
      case parse.tokens(label, src) {
        Error(err) -> {
          io.println_error("❌ " <> e.display_syntax(err))
          #([], [err])
        }
        Ok(toks) -> {
          io.println("// " <> int.to_string(list.length(toks)) <> " tokens")
          list.map(toks, fn(tok) {
            io.println(render_token(tok))
            Nil
          })
          io.println("")
          case parse.parse_statements(label, src) {
            Ok(parse.Parsed(stmts)) -> {
              io.println(">> parse -> module")
              io.println("OK")
              io.println(string.inspect(stmts))
              io.println("")
              #([#(label, stmts)], [])
            }
            Ok(parse.ParseFailed(dead_ends)) -> {
              io.println(">> parse -> module")
              print_dead_ends(dead_ends)
              let best = parse.dead_ends_to_error(label, dead_ends)
              io.println(">> best error (what the user sees)")
              io.println("❌ " <> e.display_syntax(best))
              io.println("")
              #([], [best])
            }
            Error(err) -> {
              io.println_error("❌ " <> e.display_syntax(err))
              #([], [err])
            }
          }
        }
      }
    }
  }
}

/// Render one token as `  <row>:<col>  "<lexeme>"  <constructor>`.
fn render_token(tok: lexer.Token(ParseToken)) -> String {
  let span = tok.span
  let pos =
    int.to_string(span.row_start) <> ":" <> int.to_string(span.col_start)
  "  " <> pad(pos, 8) <> " \"" <> tok.lexeme <> "\"  "
  <> string.inspect(tok.value)
}

/// Render every dead end, sorted furthest-first (the most informative
/// failure first), each with its position, problem and context stack.
fn print_dead_ends(dead_ends: List(nibble.DeadEnd(ParseToken, String))) {
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

/// Render a nibble parse problem, keeping token constructors (via
/// inspect) so a parser developer sees the exact tokens involved.
fn render_problem(problem: nibble.Error(ParseToken)) -> String {
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

// ============================================================================
// --trace defines / holes
// ============================================================================

/// `--trace defines`: the per-module definition listing.
fn defines_listing(defs: List(#(String, List(#(String, tao.Stmt))))) -> Nil {
  let _ =
    list.map(defs, fn(def) {
      let #(mod_name, mod_defs) = def
      io.println(string.inspect(mod_name) <> ":")
      list.map(mod_defs, fn(local) {
        let #(name, stmt) = local
        io.println("  - " <> string.inspect(name) <> ": " <> stmt_kind(stmt))
        Nil
      })
      Nil
    })
  Nil
}

/// A short label for a statement's kind (for the definitions listing).
fn stmt_kind(stmt: tao.Stmt) -> String {
  case stmt.data {
    tao.Import(path, _, _) -> "import " <> path
    tao.Extern(_, _, _) -> "extern"
    tao.LetVar(_, _, _) -> "let-var"
    tao.LetPat(_, _, _) -> "let-pat"
    tao.LetMut(_, _, _) -> "let-mut"
    tao.Mut(_, _) -> "mut"
    tao.Test(_, _, _) -> "test"
    tao.FnDef(_, _, _, _, _) -> "fn"
    tao.FnOverload(_, _) -> "fn-overload"
    tao.TypeDef(_, _) -> "type"
    tao.For(_, _, _) -> "for"
    tao.While(_, _) -> "while"
    tao.Return(_) -> "return"
    tao.Break -> "break"
    tao.Continue -> "continue"
  }
}

/// `--trace holes`: the hole substitution table — solved IDs and each
/// solution displayed against its captured solve env (so `$N` indices
/// are valid), plus the total hole and deferred-constraint counts.
fn holes_dump(ctx: Context, label: String) -> Nil {
  let subst = list.sort(ctx.subst, fn(a, b) { int.compare(a.0, b.0) })
  io.println(
    "// holes (" <> label <> "): subst="
      <> int.to_string(list.length(subst))
      <> " holes="
      <> int.to_string(ctx.hole_counter)
      <> " deferred="
      <> int.to_string(list.length(ctx.deferred)),
  )
  let _ =
    list.map(subst, fn(entry) {
      let #(id, #(env, value)) = entry
      let env_names =
        int.range(from: 0, to: list.length(env) - 1, with: [], run: list.prepend)
        |> list.map(fn(i) { "$" <> int.to_string(i) })
      let solution = format.value(ffi.build, env_names, value, 80, 2)
      io.println(
        "h"
          <> int.to_string(id)
          <> " (envlen="
          <> int.to_string(list.length(env))
          <> "): "
          <> string.slice(solution, 0, 200),
      )
      Nil
    })
  Nil
}

// ============================================================================
// --dump-def
// ============================================================================

/// `--dump-def <name>`: print the named definition's type value with
/// its de Bruijn structure (quantifier bodies via `format.term`),
/// searching every input module.
fn dump_def(ctx: Context, mods: List(Module), name: String) -> Nil {
  case find_def(ctx, mods, name) {
    Some(typ) -> {
      let names =
        int.range(from: 0, to: 15, with: [], run: list.prepend)
        |> list.map(fn(i) { "n" <> int.to_string(i) })
      io.println(
        "// type of "
          <> name
          <> " (names n0..n15 are de Bruijn indices)",
      )
      dump_type_value(typ, 0, names)
    }
    None -> io.println_error("definition not found: " <> name)
  }
}

fn find_def(ctx: Context, mods: List(Module), name: String) -> Option(v.Type) {
  case mods {
    [] -> None
    [#(mod_name, _), ..rest] ->
      case define.get_var(ctx, mod_name, name) {
        Some(#(_, typ)) -> Some(typ)
        None -> find_def(ctx, rest, name)
      }
  }
}

/// Print a type value's de Bruijn structure: `For`/`Pi` bodies are
/// lifted via `format.term` (a flat names list, so each `Var` shows the
/// index it addresses); other values are sketched one level deep.
/// Cycles through captured envs are never followed, so it terminates on
/// any value.
fn dump_type_value(value: v.Value, depth: Int, names: List(String)) -> Nil {
  let pad = string.join(list.repeat("  ", depth), "")
  case value {
    v.For(env, #(name, _), body) -> {
      let header =
        pad
          <> "FOR "
          <> name
          <> " (envlen="
          <> int.to_string(list.length(env))
          <> ")"
      let _ = io.println(header)
      let _ = io.println(pad <> "  body:\n" <> format.term(names, body, 80, 2))
    }
    v.Pi(env, #(_, domain), codomain) -> {
      let _ =
        io.println(
          pad
            <> "PI (envlen="
            <> int.to_string(list.length(env))
            <> ") domain="
            <> dump_sketch(domain),
        )
      let _ = io.println(pad <> "  codomain:\n" <> format.term(names, codomain, 80, 2))
    }
    other -> {
      let _ = io.println(pad <> dump_sketch(other))
    }
  }
}

/// One-level sketch (safe on cyclic values; never follows captured
/// envs).
fn dump_sketch(value: v.Value) -> String {
  case value {
    v.Neut(v.NVar(l)) -> "NVar("
      <> int.to_string(l)
      <> ")"
    v.Neut(v.NHole(_, Some(i))) -> "NHole(h" <> int.to_string(i) <> ")"
    v.Neut(v.NHole(_, None)) -> "NHole"
    v.Neut(v.NApp(..)) -> "NApp"
    v.Neut(v.NCall(..)) -> "NCall"
    v.Neut(v.NMatch(..)) -> "NMatch"
    v.Rcd(fields, tail) -> {
      let inner =
        list.map(fields, fn(field) {
          let #(_, #(fv, _)) = field
          field.0 <> ":" <> dump_sketch(fv)
        })
        |> list.fold("", fn(acc, s) { acc <> "|" <> s })
      "Rcd["
        <> inner
        <> "]"
        <> case tail {
          Some(t) -> "/" <> dump_sketch(t)
          None -> "/_"
        }
    }
    v.Typ(u) -> "Typ("
      <> int.to_string(u)
      <> ")"
    v.Lit(_) -> "Lit"
    v.LitT(_) -> "LitT"
    v.Ctr(tag, arg) -> "Ctr("
      <> tag
      <> ", "
      <> dump_sketch(arg)
      <> ")"
    v.For(..) -> "For"
    v.Lam(..) -> "Lam"
    v.Pi(..) -> "Pi"
    v.Fix(..) -> "Fix"
    v.TypeDef(..) -> "TypeDef"
    v.Err -> "Err"
  }
}
