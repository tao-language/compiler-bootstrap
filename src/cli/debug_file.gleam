import core/context.{new_ctx}
import core/format as core_format
import gleam/int
import gleam/io
import gleam/list
import gleam/result
import gleam/string
import syntax/span.{Span}
import tao/ast as tao
import tao/compile
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
  let ctx = compile.package(new_ctx, pkg)
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

  io.println("> module = load.module(filename)")
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

  let tests = discover.tests(stmts)
  io.println("  tests: " <> int.to_string(list.length(tests)) <> " length")
  list.map(tests, fn(t) {
    let #(name, expr, expect) = t
    io.println("  - " <> name)
  })
  io.println("")

  todo
}
