import core/ast as core
import core/context.{Context, new_ctx}
import core/error
import core/eval.{eval}
import core/ffi
import core/format as core_format
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
  case ctx.errors {
    [] -> Nil
    errors -> {
      let n = list.length(errors)
      io.println_error("---- BUILD ERRORS (" <> int.to_string(n) <> ") ----")
      list.map(ctx.errors, fn(err) {
        let msg = error.display(ctx.ffi, ctx.types, err)
        io.println_error(msg)
      })
      io.println_error("---- BUILD ERRORS END ----")
    }
  }
  let names = list.map(ctx.types, fn(t) { t.0 })
  io.println("ffi: " <> int.to_string(list.length(ctx.ffi)) <> " length")
  list.map(ctx.ffi, fn(entry) {
    let #(name, _) = entry
    io.println("- " <> name)
  })
  io.println("env:   " <> int.to_string(list.length(ctx.env)) <> " length")
  io.println("types: " <> int.to_string(list.length(ctx.types)) <> " length")
  list.map(ctx.types, fn(entry) {
    let #(name, type_) = entry
    io.println(
      "- \""
      <> name
      <> "\": "
      <> core_format.value(ctx.ffi, names, type_, width, 2),
    )
  })
  // io.println("subst: " <> int.to_string(list.length(ctx.subst)) <> " length")
  // list.map(ctx.subst, fn(entry) {
  //   let #(id, value) = entry
  //   io.println(
  //     "  - "
  //     <> int.to_string(id)
  //     <> ": "
  //     <> core_format.value(ctx.ffi, names, value, width, 2),
  //   )
  // })
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
  io.println(core_format.expr(mod_expr, width, 2))
  io.println("")

  echo "> definition types"
  list.map(definitions, fn(name) {
    let def_expr = core.dot(mod_expr, name, s)
    // DO NOT update the ctx, it's already been fully resolved.
    // Updating the context will cause duplicate errors.
    // This is only to debug/view the definition types.
    let #(term, def_type, _) = infer(ctx, def_expr)
    let def_type = resolve.value(ctx.ffi, ctx.subst, ctx.env, def_type)
    let names = list.map(ctx.types, fn(entry) { entry.0 })
    io.println("name: " <> name)
    io.println(
      "type: " <> core_format.value(ctx.ffi, names, def_type, width, 2),
    )
    io.println("value: " <> core_format.term(names, term, width, 2))
    io.println("")
  })

  echo "> tests = compile.tests(stmts)"
  let tests = compile.tests([#(filename, stmts)])
  let names = list.map(ctx.types, fn(entry) { entry.0 })
  list.map(tests, fn(t) {
    let core_expr = desugar.expr(t.expr)
    let core_expect = desugar.pattern(t.expect)
    // DO NOT update the ctx, it's already been fully resolved.
    // Updating the context will cause duplicate errors.
    // This is only to debug/view the definition types.
    let #(_, def_type, _) = infer(ctx, core_expr)
    let value = eval(ctx.ffi, ctx.env, t.term)
    io.println("/// " <> t.name)
    io.println(">>> " <> core_format.expr(core_expr, width, 2))
    io.println(
      "type:   " <> core_format.value(ctx.ffi, names, def_type, width, 2),
    )
    io.println("expect: " <> core_format.pattern(core_expect, width, 2))
    io.println("got:    " <> core_format.value(ctx.ffi, names, value, width, 2))
    io.println("")
  })

  io.println("---- SUMMARY ----")
  io.println(int.to_string(list.length(ctx.errors)) <> " build errors")
}
