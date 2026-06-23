import core/context.{Context, new_ctx}
import core/eval.{eval}
import core/ffi
import core/format as core_format
import core/infer.{infer}
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

pub fn debug_file(root: String, filename: String, width: Int) {
  io.println("root: " <> root)
  io.println("filename: " <> filename)
  io.println("")

  io.println("> pkg = load.package(root)")
  let #(pkg, errors) =
    fs.list_recursive(root, string.ends_with(_, ".tao"))
    |> result.unwrap([])
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

  io.println("> ctx = compile.package(pkg)")
  let ctx = Context(..new_ctx, ffi: ffi.build)
  let ctx = compile.package(ctx, pkg)
  case list.length(errors) {
    0 -> Nil
    n -> {
      io.println("--- " <> int.to_string(n) <> " errors ---")
      todo as "print errors"
      io.println("")
    }
  }
  let names = list.map(ctx.types, fn(t) { t.0 })
  io.println("  env:   " <> int.to_string(list.length(ctx.env)) <> " length")
  io.println("  types: " <> int.to_string(list.length(ctx.types)) <> " length")
  list.map(ctx.types, fn(entry) {
    let #(name, type_) = entry
    io.println(
      "  - \""
      <> name
      <> "\": "
      <> core_format.value(ctx.ffi, names, type_, width, 2),
    )
  })
  io.println("  subst: " <> int.to_string(list.length(ctx.subst)) <> " length")
  list.map(ctx.subst, fn(entry) {
    let #(id, value) = entry
    io.println(
      "  - "
      <> int.to_string(id)
      <> ": "
      <> core_format.value(ctx.ffi, names, value, width, 2),
    )
  })
  io.println("  ffi:   " <> int.to_string(list.length(ctx.ffi)) <> " length")
  list.map(ctx.ffi, fn(entry) {
    let #(name, _) = entry
    io.println("  - " <> name)
  })
  io.println("")

  io.println("> stmts = load.module(filename)")
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
    "  definitions: " <> int.to_string(list.length(definitions)) <> " length",
  )
  list.map(definitions, fn(name) { io.println("  - " <> name) })
  io.println("")

  io.println("> test_defs = discover.tests(stmts)")
  let test_defs = discover.tests(stmts)
  let test_names = list.map(test_defs, fn(tst) { "> " <> tst.0 })
  io.println("  total tests: " <> int.to_string(list.length(test_defs)))
  list.map(test_names, fn(name) { io.println("  - " <> name) })
  io.println("")

  io.println("> mod_expr = desugar.module(stmts)")
  let mod_expr = desugar.module(#(filename, stmts), test_names)
  io.println(core_format.expr(mod_expr, width, 2))
  io.println("")

  io.println("> tests = compile.tests(stmts)")
  let #(tests, ctx) = compile.tests(ctx, [#(filename, stmts)])
  case list.length(ctx.errors) {
    0 -> Nil
    n -> {
      io.println_error("---- ERRORS (" <> int.to_string(n) <> ") ----")
      list.map(ctx.errors, fn(e) {
        let msg = string.inspect(e)
        io.println_error("- " <> msg)
      })
      io.println_error("---- ERRORS END ----")
    }
  }
  let names = list.map(ctx.types, fn(t) { t.0 })
  list.map(tests, fn(t) {
    let value = eval(ctx.ffi, ctx.env, t.term)
    io.println(
      "  - "
      <> t.name
      <> ": "
      <> core_format.value(ctx.ffi, names, value, width, 2),
    )
  })
  io.println("")

  io.println("---- SUMMARY ----")
  io.println(int.to_string(list.length(ctx.errors)) <> " build errors")
}
