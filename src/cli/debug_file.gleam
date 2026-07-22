import core/context.{Context, new_ctx}
import core/error
import core/eval.{eval}
import core/ffi
import core/format
import core/resolve
import core/unwrap
import core/value as v
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option}
import gleam/result
import gleam/string
import tao/compile
import tao/desugar
import tao/discover
import tao/load
import utils/fs

pub fn debug_file(
  src_dir: String,
  paths: List(String),
  packages: List(#(String, Option(String))),
  filename: String,
  width: Int,
) {
  io.println("src_dir: " <> string.inspect(src_dir))
  io.println("paths: " <> string.inspect(paths))
  io.println("packages: " <> string.inspect(packages))
  io.println("filename: " <> filename)
  io.println("")

  echo "> load.module(filename)"
  let #(mod, errors) = load.module([src_dir], filename)
  let #(mods, errors) = case src_dir {
    "" -> #([mod], errors)
    _ -> {
      echo "> load.directory(src_dir)"
      let #(mods, err) = load.directory(src_dir)
      #([mod, ..mods], list.append(errors, err))
    }
  }
  echo "> load.package_list(paths, packages)"
  let #(pkg_mods, pkg_errors) = load.package_list(paths, packages)
  let #(mods, errors) = #(
    list.append(mods, pkg_mods),
    list.append(errors, pkg_errors),
  )
  io.println("modules loaded: " <> int.to_string(list.length(mods)))
  list.map(mods, fn(mod) { io.println("- " <> mod.0) })
  io.println("")

  case list.length(errors) {
    0 -> Nil
    n -> {
      io.println_error("---- SYNTAX ERRORS ----")
      list.map(errors, fn(err) {
        let msg = error.display_syntax(err)
        io.println_error("❌ " <> msg)
      })
      io.println("")
      io.println_error(int.to_string(n) <> " syntax errors")
      exit(1)
    }
  }

  let names = list.map(mods, fn(m) { m.0 })
  let fmt_expr = fn(expr) { format.expr(expr, width, 2) }
  let fmt_term = fn(term) { format.term(names, term, width, 2) }
  let fmt_value = fn(val) { format.value(ffi.build, names, val, width, 2) }
  let fmt_pattern = fn(pat) { format.pattern(pat, width, 2) }

  echo "> stmts = load.module(filename)"
  let #(#(name, stmts), errors) = load.module(paths, filename)
  io.println("module name: " <> string.inspect(name))
  case list.length(errors) {
    0 -> Nil
    n -> {
      io.println_error("---- SYNTAX ERRORS ----")
      list.map(errors, fn(err) {
        let msg = error.display_syntax(err)
        io.println_error("❌ " <> msg)
      })
      io.println("")
      io.println_error(int.to_string(n) <> " syntax errors")
      exit(1)
    }
  }
  let exports = discover.definitions(stmts)
  io.println("exports: " <> int.to_string(list.length(exports)) <> " length")
  list.map(exports, fn(name) { io.println("- " <> name) })
  io.println("")

  echo "> defs, mods_defs = compile.definitions(mods)"
  let mods_defs = compile.definitions(mods)
  let defs = list.map(mods_defs, fn(m) { #(m.0, m.1) })
  list.map(defs, fn(def) {
    let #(name, exports) = def
    io.println("- " <> string.inspect(name) <> ":")
    list.map(exports, fn(x) { io.println("  - " <> string.inspect(x)) })
  })
  io.println("")

  let ctx = Context(..new_ctx, ffi: ffi.build)
  io.println("ffi (" <> int.to_string(list.length(ctx.ffi)) <> ")")
  list.map(ctx.ffi, fn(entry) {
    let #(name, _) = entry
    io.println("- " <> name)
  })
  io.println("")

  echo "> core_mods = compile.define_modules(defs, mods)"
  let #(core_mods, ctx) = compile.define_modules(ctx, defs, mods_defs)
  list.map(list.zip(defs, core_mods), fn(pair) {
    let #(#(name, _), mod) = pair
    let #(value_id, type_id, mod_expr) = mod
    io.println(
      "//--- "
      <> name
      <> ": value_hole_id="
      <> int.to_string(value_id)
      <> " type_hole_id="
      <> int.to_string(type_id),
    )
    io.println(fmt_expr(mod_expr))
    io.println("")
  })
  list.map(list.zip(ctx.types, ctx.env), fn(entry) {
    let #(#(name, mod_type), mod_value) = entry
    io.println("// ctx.env[" <> string.inspect(name) <> "]")
    io.println(fmt_value(mod_value))
    io.println("// ctx.types[" <> string.inspect(name) <> "]")
    io.println(fmt_value(mod_type))
    io.println("")
  })
  io.println("")

  echo "> compile.infer_modules(core_mods)"
  let ctx = compile.infer_modules(ctx, core_mods)
  list.map(list.zip(ctx.types, ctx.env), fn(entry) {
    let #(#(name, mod_type), mod_value) = entry
    // Unwrap to at least see the initial structure directly
    let mod_value = unwrap.unwrap(ctx.ffi, ctx.subst, mod_value)
    let mod_type = unwrap.unwrap(ctx.ffi, ctx.subst, mod_type)
    io.println("// ctx.env[" <> string.inspect(name) <> "]")
    io.println(fmt_value(mod_value))
    io.println("// ctx.types[" <> string.inspect(name) <> "]")
    io.println(fmt_value(mod_type))
    io.println("")
  })
  io.println(
    "// ctx.subst: " <> int.to_string(list.length(ctx.subst)) <> " solved holes",
  )
  io.println(
    "// solved: " <> string.inspect(list.map(ctx.subst, fn(kv) { kv.0 })),
  )
  // list.map(ctx.subst, fn(entry) {
  //   let #(id, value) = entry
  //   // TODO: save ctx.types.names in ctx.subst to display var names.
  //   let fmt_subst = format.value(ctx.ffi, [], value, width, 2)
  //   io.println("- " <> int.to_string(id) <> ": " <> fmt_subst)
  // })
  io.println("")

  echo "> resolve.context(ctx)"
  let ctx = resolve.context(ctx)
  list.map(list.zip(ctx.types, ctx.env), fn(entry) {
    let #(#(name, mod_type), mod_value) = entry
    io.println("// ctx.env[" <> string.inspect(name) <> "]")
    io.println(fmt_value(mod_value))
    io.println("// ctx.types[" <> string.inspect(name) <> "]")
    io.println(fmt_value(mod_type))
    io.println("")
  })

  case ctx.errors {
    [] -> io.println("0 build errors")
    errors -> {
      let n = list.length(errors)
      io.println_error("---- BUILD ERRORS ----")
      list.map(ctx.errors, fn(err) {
        let msg = error.display(ctx.ffi, ctx.types, err)
        io.println_error("❌ " <> msg)
      })
      io.println("")
      io.println_error(int.to_string(n) <> " build errors")
      exit(1)
    }
  }

  echo "> tests = compile.tests(stmts)"
  let tests = compile.tests([#(filename, stmts)])
  let test_results =
    list.map(tests, fn(t) {
      let core_expr = desugar.expr(defs, t.expr)
      let core_expect = desugar.pattern(t.expect)
      let value = eval(ctx.ffi, ctx.env, t.term)
      io.println("/// " <> t.name)
      io.println(">>> " <> fmt_expr(core_expr))
      io.println(fmt_pattern(core_expect))
      io.println("result: " <> fmt_value(value))
      // io.println("test-term: " <> fmt_term(t.term))
      io.println("")
      value
    })

  let #(passed, failed, unknown) =
    list.fold(test_results, #(0, 0, 0), fn(acc, value) {
      let #(passed, failed, unknown) = acc
      case value {
        v.Ctr("Pass", _) -> #(passed + 1, failed, unknown)
        v.Ctr("Fail", _) -> #(passed, failed + 1, unknown)
        _ -> #(passed, failed, unknown + 1)
      }
    })

  io.println("test results")
  io.println("- " <> int.to_string(list.length(test_results)) <> " total")
  io.println("- " <> int.to_string(passed) <> " passed")
  io.println("- " <> int.to_string(failed) <> " failed")
  case unknown {
    0 -> Nil
    _ -> io.println("- " <> int.to_string(unknown) <> " unkown result state")
  }
  io.println("")
}

// Declare the external Erlang halt function
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil
