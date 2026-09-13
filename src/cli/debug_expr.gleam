/// `tao debug-expr` — parse a Tao expression, then run it through the
/// whole Tao → Core pipeline, printing every stage:
///
///   parse    Tao source → Tao Expr
///   scope    load the prelude (auto-imported) + extra packages, run
///            declare/define/resolve over them, and bring their names
///            into scope (the scaffolding the expression is checked in)
///   desugar  Tao Expr → Core Expr (named terms)
///   infer    Core Expr → (Term, Type) via bidirectional type checking
///   resolve  fill every solved hole in the Term and Type
///   eval     Term → Value (normalization)
///
/// Unlike `debug-file` (which debugs a whole module: its definitions,
/// hole resolution, tests), this focuses on a single expression.
import core/ast
import core/context.{type Context, Context, new_ctx}
import core/error
import core/eval.{eval}
import core/ffi
import core/format
import core/infer.{infer}
import core/resolve
import core/value as v
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import tao/ast.{type Expr, type Module, type Stmt} as tao
import tao/declare
import tao/define
import tao/desugar
import tao/load
import tao/parse.{expression as parse_expression}

pub fn debug_expr(
  paths: List(String),
  packages: List(#(String, Option(String))),
  source: String,
  width: Int,
) -> Nil {
  io.println(">> source")
  io.println(source)
  io.println("")

  io.println(">> parse(source) -> Tao Expr")
  case parse_expression("<debug-expr>", source) {
    Error(err) -> {
      io.println_error("❌ " <> error.display_syntax(err))
      io.println("")
      io.println_error("1 syntax error")
      exit(1)
    }
    Ok(expr) -> {
      io.println(string.inspect(expr))
      io.println("")
      debug_pipeline(paths, packages, expr, width)
    }
  }
}

/// Run the parsed expression through desugar → infer → resolve → eval
/// against a context with the prelude and any extra packages loaded and
/// their names in scope, printing each stage.
fn debug_pipeline(
  paths: List(String),
  packages: List(#(String, Option(String))),
  expr: Expr,
  width: Int,
) -> Nil {
  // ── Stage 0: build the scaffolding context ───────────────────────
  // The prelude (standard library) is loaded automatically; `packages`
  // holds any extra packages given on the command line.
  let packages = list.append(packages, [#("prelude", None)])
  io.println(
    ">> load.package_list(" <> string.inspect(paths) <> ", packages)",
  )
  let #(mods, errors) = load.package_list(paths, packages)
  io.println("modules loaded: " <> int.to_string(list.length(mods)))
  list.map(mods, fn(mod) { io.println("  - " <> mod.0) })
  io.println("")

  case list.length(errors) {
    0 -> Nil
    n -> {
      io.println_error("---- SYNTAX ERRORS ----")
      list.map(errors, fn(err) {
        io.println_error("❌ " <> error.display_syntax(err))
      })
      io.println_error("")
      io.println_error(int.to_string(n) <> " syntax errors")
      exit(1)
    }
  }

  let ctx = Context(..new_ctx, ffi: ffi.build)

  echo "> defs = declare.modules(mods)"
  let defs = declare.modules(mods)
  list.map(defs, fn(def) {
    let #(mod_name, mod_defs) = def
    io.println(string.inspect(mod_name) <> ":")
    list.map(mod_defs, fn(local) {
      let #(name, stmt) = local
      io.println("  - " <> string.inspect(name) <> ": " <> stmt_kind(stmt))
    })
  })
  io.println("")

  echo "> ctx = define.types(ctx, defs)"
  let ctx = define.types(ctx, defs)
  echo "> ctx = define.values(ctx, defs)"
  let ctx = define.values(ctx, defs)
  holes_summary(ctx, 0, "loaded modules", width)

  echo "> ctx = resolve.context(ctx)"
  let ctx = resolve.context(ctx)
  let prelude_errors = ctx.errors
  let prelude_holes = ctx.hole_counter
  case list.length(prelude_errors) {
    0 -> io.println("0 errors in the loaded modules")
    n -> {
      io.println_error("---- MODULE BUILD ERRORS ----")
      list.map(prelude_errors, fn(err) {
        io.println_error("❌ " <> error.display(ctx.ffi, ctx.types, err))
      })
      io.println_error("")
      io.println_error(int.to_string(n) <> " build errors")
    }
  }
  io.println("")

  echo "> push the loaded modules' public names into scope"
  let ctx = push_loaded_names(ctx, mods)
  let names = list.map(ctx.types, fn(entry) { entry.0 })
  io.println("in scope (" <> int.to_string(list.length(names)) <> "): ")
  list.map(names, fn(name) { io.println("  - " <> name) })
  io.println("")

  // ── Stage 1: desugar Tao → Core (named terms) ────────────────────
  io.println(">> desugar(expr) -> Core Expr")
  let exports = declare.exports(defs)
  let core_expr = desugar.expr(exports, expr)
  io.println(format.expr(core_expr, width, 2))
  io.println(
    "// free variables: "
      <> string.inspect(ast.free_vars(core_expr)),
  )
  io.println("")

  // ── Stage 2: type inference / checking ───────────────────────────
  io.println(">> infer(ctx, core_expr) -> #(Term, Type)")
  let #(term, type_, ctx) = infer(ctx, core_expr)

  let errors =
    list.map(ctx.errors, fn(err) {
      resolve.error(ctx.ffi, ctx.subst, ctx.env, err)
    })
  let new_errors =
    list.filter(errors, fn(err) { !list.contains(prelude_errors, err) })
  case list.length(new_errors) {
    0 -> io.println("// no errors")
    n -> {
      io.println("// Errors (" <> int.to_string(n) <> ")")
      list.map(new_errors, fn(err) {
        io.println("❌ " <> error.display(ctx.ffi, ctx.types, err))
      })
      Nil
    }
  }

  let names = list.map(ctx.types, fn(entry) { entry.0 })
  let fmt_value = fn(val: v.Value) {
    format.value(ctx.ffi, names, val, width, 2)
  }

  io.println("// Type (inferred)")
  io.println(fmt_value(type_))
  io.println("")
  io.println("// Term (inferred, holes unresolved)")
  io.println(format.term(names, term, width, 2))
  io.println("")

  io.println("// Deferred constraints (not yet decidable)")
  io.println("//   " <> int.to_string(list.length(ctx.deferred)))
  io.println("")

  holes_summary(ctx, prelude_holes, "expression", width)

  // ── Stage 3: resolve (fill solved holes in term and type) ────────
  io.println(">> resolve(subst, term, type)")
  let term = resolve.term(ctx.ffi, ctx.subst, ctx.env, term)
  let type_ = resolve.value(ctx.ffi, ctx.subst, type_)
  io.println("// Type (resolved)")
  io.println(fmt_value(type_))
  io.println("")
  io.println("// Term (resolved)")
  io.println(format.term(names, term, width, 2))
  io.println("")

  // ── Stage 4: evaluate (normalize) ────────────────────────────────
  io.println(">> eval(ctx.env, term) -> Value")
  let value = eval(ctx.ffi, ctx.env, term)
  io.println(fmt_value(value))
  io.println("")

  case list.length(new_errors) + list.length(prelude_errors) {
    0 -> Nil
    _ -> exit(1)
  }
}

/// Print a compact hole summary: how many holes in total, how many
/// belong to the current stage (IDs ≥ `from`), which are solved and
/// which are not, and the solution of each solved hole.
fn holes_summary(
  ctx: Context,
  from: Int,
  label: String,
  width: Int,
) {
  let subst =
    list.filter(ctx.subst, fn(entry) { entry.0 >= from })
    |> list.sort(fn(a, b) { int.compare(a.0, b.0) })
  let solved = list.map(subst, fn(entry) { entry.0 })
  let all =
    int.range(ctx.hole_counter - 1, -1, [], list.prepend)
    |> list.filter(fn(id) { id >= from })
  let unsolved = list.filter(all, fn(id) { !list.contains(solved, id) })
  let names = list.map(ctx.types, fn(entry) { entry.0 })
  io.println(
    "// Holes (" <> label <> "): "
      <> int.to_string(list.length(all))
      <> " of "
      <> int.to_string(ctx.hole_counter)
      <> " total",
  )
  io.println(
    "//   "
      <> int.to_string(list.length(subst))
      <> " solved: "
      <> string.inspect(list.map(subst, fn(e) { e.0 })),
  )
  io.println(
    "//   " <> int.to_string(list.length(unsolved)) <> " unsolved: "
      <> string.inspect(unsolved),
  )
  list.map(subst, fn(entry) {
    let #(id, #(_, value)) = entry
    io.println(
      "- ?" <> int.to_string(id) <> ": "
        <> format.value(ctx.ffi, names, value, width, 2),
    )
  })
  io.println("")
}

/// Bring every public definition of the loaded modules into scope as
/// local bindings — the same names an `import … *` would flatten into
/// a module, which `define.expr_value` pushes when checking a body.
fn push_loaded_names(ctx: Context, mods: List(Module)) -> Context {
  list.fold(mods, ctx, fn(ctx, mod) {
    let mod_name = mod.0
    case context.lookup_var(ctx, mod_name) {
      Some(#(v.Rcd(values, _), v.Rcd(types, _))) ->
        list.fold(values, ctx, fn(ctx, entry) {
          let #(name, #(val, _)) = entry
          case list.key_find(types, name) {
            Error(Nil) -> ctx
            Ok(#(typ, _)) ->
              case declare.is_public_name(name) {
                False -> ctx
                True -> context.push_var(ctx, #(name, val, typ))
              }
          }
        })
      _ -> ctx
    }
  })
}

/// A short label for a statement's kind (for the definitions listing).
fn stmt_kind(stmt: Stmt) -> String {
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

/// Terminate the process with `status`.
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil
