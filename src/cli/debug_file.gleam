import core/ast as core
import core/context.{Context, new_ctx}
import core/error
import core/eval.{eval}
import core/ffi
import core/format
import core/infer.{infer}
import core/resolve
import gleam/int
import gleam/io
import gleam/list
import gleam/result
import gleam/string
import syntax/span.{Span}
import tao/ast as tao
import tao/compile
import tao/desugar
import tao/discover
import tao/load
import utils/fs

const s = Span("debug_file", 0, 0, 0, 0)

pub fn debug_file(root: String, filename: String, width: Int) {
  io.println("root: " <> root)
  io.println("filename: " <> filename)
  io.println("")

  echo "> pkg = load.package(root)"
  let #(pkg, errors) =
    fs.list_recursive(root, string.ends_with(_, ".tao"))
    |> result.unwrap([])
    |> list.prepend(filename)
    |> load.package
  case list.length(errors) {
    0 -> Nil
    n -> {
      io.println("--- " <> int.to_string(n) <> " errors ---")
      todo as "print errors"
      io.println("")
    }
  }
  io.println("")

  echo "> ctx = compile.package(pkg)"
  let ctx = Context(..new_ctx, ffi: ffi.build)
  let ctx = compile.package(ctx, pkg)
  let names = list.map(ctx.types, fn(t) { t.0 })
  let fmt_expr = fn(expr) { format.expr(expr, width, 2) }
  let fmt_term = fn(term) { format.term(names, term, width, 2) }
  let fmt_value = fn(val) { format.value(ctx.ffi, names, val, width, 2) }
  let fmt_pattern = fn(pat) { format.pattern(pat, width, 2) }

  io.println("ffi (" <> int.to_string(list.length(ctx.ffi)) <> ")")
  list.map(ctx.ffi, fn(entry) {
    let #(name, _) = entry
    io.println("- " <> name)
  })
  io.println("")

  io.println("env (" <> int.to_string(list.length(ctx.env)) <> ")")
  list.zip(ctx.types, ctx.env)
  |> list.map(fn(entry) {
    let #(#(name, _), value) = entry
    io.println("- \"" <> name <> "\": " <> fmt_value(value))
  })
  io.println("")

  io.println("types (" <> int.to_string(list.length(ctx.types)) <> ")")
  list.map(ctx.types, fn(entry) {
    let #(name, type_) = entry
    io.println("- \"" <> name <> "\": " <> fmt_value(type_))
  })
  io.println("")

  io.println("subst (" <> int.to_string(list.length(ctx.subst)) <> ")")
  list.map(ctx.subst, fn(entry) {
    let #(id, value) = entry
    io.println("- " <> int.to_string(id) <> ": " <> fmt_value(value))
  })
  io.println("")

  echo "> stmts = load.module(filename)"
  let #(stmts, errors) = load.module(filename)
  case list.length(errors) {
    0 -> Nil
    n -> {
      io.println("--- " <> int.to_string(n) <> " errors ---")
      todo as "print errors"
      io.println("")
    }
  }
  let definitions = discover.definitions(stmts)
  io.println(
    "definitions: " <> int.to_string(list.length(definitions)) <> " length",
  )
  list.map(definitions, fn(name) { io.println("- " <> name) })
  io.println("")

  echo "> mod_expr = desugar.module(stmts, definitions)"
  let mod_expr = desugar.module(#(filename, stmts), definitions)
  io.println(fmt_expr(mod_expr))
  io.println("")

  echo "> definition types"
  list.map(definitions, fn(name) {
    let def_expr = core.dot(mod_expr, name, s)
    // DO NOT update the ctx, it's already been fully resolved.
    // Updating the context will cause duplicate errors.
    // This is only to debug/view the definition types.
    let #(term, def_type, _) = infer(ctx, def_expr)
    let def_type = resolve.value(ctx.ffi, ctx.subst, def_type)
    io.println("/// " <> name)
    io.println(fmt_expr(def_expr))
    io.println("term: " <> fmt_term(term))
    io.println("type: " <> fmt_value(def_type))
    io.println("")
  })

  echo "> tests = compile.tests(stmts)"
  let tests = compile.tests([#(filename, stmts)])
  list.map(tests, fn(t) {
    let core_expr = desugar.expr(t.expr)
    let core_expect = desugar.pattern(t.expect)
    // DO NOT update the ctx, it's already been fully resolved.
    // Updating the context will cause duplicate errors.
    // This is only to debug/view the definition types.
    let #(_, def_type, _) = infer(ctx, core_expr)
    let value = eval(ctx.ffi, ctx.env, t.term)
    io.println("/// " <> t.name)
    io.println(">>> " <> fmt_expr(core_expr))
    io.println("term:   " <> fmt_term(t.term))
    io.println("type:   " <> fmt_value(def_type))
    io.println("expect: " <> fmt_pattern(core_expect))
    io.println("got:    " <> fmt_value(value))
    io.println("")
  })

  case ctx.errors {
    [] -> io.println("0 build errors")
    errors -> {
      let n = list.length(errors)
      io.println_error("---- " <> int.to_string(n) <> " build errors ----")
      list.map(ctx.errors, fn(err) {
        let msg = error.display(ctx.ffi, ctx.types, err)
        io.println_error(msg)
      })
      Nil
    }
  }
}
