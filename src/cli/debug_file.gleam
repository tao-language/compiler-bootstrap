import core/context.{Context, new_ctx}
import core/error
import core/ffi
import core/format
import core/resolve
import core/unwrap
import core/value as v
import filepath
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string
import tao/ast.{type Module, type Stmt} as tao
import tao/compile
import tao/declare
import tao/define
import tao/desugar
import tao/load
import tao/tests
import utils/fs

/// `tao debug-file` — load the project (plus dependencies), run the full
/// compile pipeline with per-phase output, then run the tests. Exits
/// non-zero on syntax errors, build errors, or failed tests.
pub fn debug_file(
  src_dir: String,
  paths: List(String),
  packages: List(#(String, Option(String))),
  filename: String,
  width: Int,
) -> Nil {
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
  // Make prelude (standard library) names available in every module.
  let mods = load.implicit_prelude_imports(mods, pkg_mods)
  io.println("modules loaded: " <> int.to_string(list.length(mods)))
  list.map(mods, fn(mod) { io.println("  - " <> mod.0) })
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

  // echo "> stmts = load.module(filename)"
  // let #(#(name, stmts), errors) = load.module(paths, filename)
  // io.println("module name: " <> string.inspect(name))
  // case list.length(errors) {
  //   0 -> Nil
  //   n -> {
  //     io.println_error("---- SYNTAX ERRORS ----")
  //     list.map(errors, fn(err) {
  //       let msg = error.display_syntax(err)
  //       io.println_error("❌ " <> msg)
  //     })
  //     io.println("")
  //     io.println_error(int.to_string(n) <> " syntax errors")
  //     exit(1)
  //   }
  // }

  // Define helpers to print and format.
  let ctx = Context(..new_ctx, ffi: ffi.build)
  let names = list.map(ctx.types, fn(x) { x.0 })
  let fmt_expr = fn(expr) { format.expr(expr, width, 2) }
  let fmt_value = fn(val) { format.value(ffi.build, names, val, width, 2) }

  echo "> defs = declare.modules(mods)"
  let defs = declare.modules(mods)
  list.map(defs, fn(def) {
    let #(mod_name, mod_defs) = def
    io.println(string.inspect(mod_name) <> ":")
    list.map(mod_defs, fn(local) {
      let #(name, stmt) = local
      let stmt_str = case stmt.data {
        tao.Import(path, alias, scope) -> "import " <> path
        tao.Extern(name, params, returns) -> "extern"
        tao.LetVar(name, opt_type, value) -> "let-var"
        tao.LetPat(pattern, types, value) ->
          "let-pat " <> string.inspect(pattern)
        tao.LetMut(name, opt_type, value) -> "let-mut"
        tao.Mut(name, value) -> todo
        tao.Test(name, expr, expect) -> "test"
        tao.FnDef(name, implicits, params, returns, body) -> "fn"
        tao.FnOverload(name, choices) -> "fn-overload"
        tao.TypeDef(type_def) -> todo
        tao.For(iterator, range, body) -> todo
        tao.While(condition, body) -> todo
        tao.Return(expr) -> todo
        tao.Break -> todo
        tao.Continue -> todo
      }
      io.println("  - " <> string.inspect(name) <> ": " <> stmt_str)
    })
  })
  io.println("")

  echo "> ctx = define.types(ctx, defs, mods)"
  let ctx = define.types(ctx, defs)
  list.map(list.zip(ctx.types, ctx.env), fn(entry) {
    let #(#(name, mod_type), mod_value) = entry
    io.print("ctx.env[" <> string.inspect(name) <> "]: ")
    io.println(fmt_value(mod_value))
    io.print("ctx.types[" <> string.inspect(name) <> "]: ")
    io.println(fmt_value(mod_type))
    io.println("")
  })

  echo "> ctx = define.values(ctx, defs)"
  let ctx = define.values(ctx, defs)
  list.map(list.zip(ctx.types, ctx.env), fn(entry) {
    let #(#(name, mod_type), mod_value) = entry
    io.print("ctx.env[" <> string.inspect(name) <> "]: ")
    io.println(fmt_value(mod_value))
    // io.print("ctx.types[" <> string.inspect(name) <> "]: ")
    // io.println(fmt_value(mod_type))
    io.println("")
  })

  echo "> ctx.subst"
  let subst = list.sort(ctx.subst, fn(a, b) { int.compare(a.0, b.0) })
  let solved = list.map(subst, fn(entry) { entry.0 })
  let unsolved =
    int.range(ctx.hole_counter - 1, -1, [], list.prepend)
    |> list.filter(fn(id) { !list.contains(solved, id) })
  io.println("// " <> int.to_string(ctx.hole_counter) <> " holes total")
  io.println(
    "// "
    <> int.to_string(list.length(unsolved))
    <> " unsolved: "
    <> string.inspect(unsolved),
  )
  io.println(
    "// "
    <> int.to_string(list.length(solved))
    <> " solved: "
    <> string.inspect(solved),
  )
  // Uncomment to view hole solution values.
  // list.map(subst, fn(entry) {
  //   let #(id, value) = entry
  //   io.println("- " <> int.to_string(id) <> ": " <> fmt_value(value))
  // })
  io.println("")

  echo "> resolve.context(ctx)"
  let ctx = resolve.context(ctx)
  list.index_map(list.zip(ctx.types, ctx.env), fn(entry, index) {
    let #(#(name, mod_type), mod_value) = entry
    let idx = int.to_string(index)
    io.println("// " <> idx <> ": ctx.env[" <> string.inspect(name) <> "]")
    io.println(fmt_value(mod_value))
    io.println("// " <> idx <> ": ctx.types[" <> string.inspect(name) <> "]")
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
  io.println("")

  echo "> test_defs, ctx = compile.tests(ctx, mods)"
  let #(test_defs, ctx) = compile.tests(ctx, mods)
  let results =
    list.map(test_defs, fn(t) {
      let res = tests.run(ctx, t)
      case res {
        tests.TestPass(name) -> io.println("✓ " <> name)
        tests.TestFail(name, got, _, _) -> {
          io.println_error("✗ " <> name)
          io.println_error("  got: " <> fmt_value(got))
        }
        tests.TestNeutral(name, got, _, _) -> {
          io.println("? " <> name)
          io.println("  got: " <> fmt_value(got))
        }
      }
      res
    })
  let #(passed, failed, neutral) =
    list.fold(results, #(0, 0, 0), fn(acc, res) {
      let #(passed, failed, neutral) = acc
      case res {
        tests.TestPass(..) -> #(passed + 1, failed, neutral)
        tests.TestFail(..) -> #(passed, failed + 1, neutral)
        tests.TestNeutral(..) -> #(passed, failed, neutral + 1)
      }
    })
  io.println("")

  io.println("test results")
  io.println("- " <> int.to_string(list.length(results)) <> " total")
  io.println("- " <> int.to_string(passed) <> " passed")
  io.println("- " <> int.to_string(failed) <> " failed")
  case neutral {
    0 -> Nil
    _ -> io.println("- " <> int.to_string(neutral) <> " neutral")
  }
  case list.length(unsolved) {
    0 -> Nil
    n ->
      io.println(
        "- "
        <> int.to_string(n)
        <> " unsolved holes, "
        <> int.to_string(ctx.hole_counter)
        <> " total",
      )
  }
  io.println("")
  case failed {
    0 -> Nil
    _ -> exit(1)
  }
}

/// Terminate the process with `status`.
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil
