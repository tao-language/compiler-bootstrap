import cli/common
import core/context.{Context, new_ctx}
import core/error
import core/ffi
import core/format
import core/resolve
import filepath
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option}
import gleam/string
import tao/ast as tao
import tao/compile
import tao/declare
import tao/define
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

  let packages = common.with_prelude(packages)
  let files = case src_dir {
    "" -> [filename]
    _ ->
      case fs.list_recursive(src_dir, fn(f) { string.ends_with(f, ".tao") }) {
        Ok(rel_files) ->
          list.map(rel_files, fn(f) { filepath.join(src_dir, f) })
        Error(_) -> [filename]
      }
  }
  echo "> load.project(paths, files, packages)"
  let #(mods, errors) = load.project(paths, files, packages)
  let prelude =
    list.filter(mods, fn(m) {
      case m.0 {
        "/prelude" -> True
        "/prelude/" <> _ -> True
        _ -> False
      }
    })
  let mods = load.implicit_prelude_imports(mods, prelude)
  let pkg_names = list.map(packages, fn(p) { p.0 })
  let target_name = load.canonical_name(paths, pkg_names, filename)
  let mod =
    case list.find(mods, fn(m) { m.0 == target_name }) {
      Ok(m) -> m
      Error(Nil) -> #("", [])
    }
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
  let fmt_value = fn(val) { format.value(ffi.build, names, val, width, 2) }

  echo "> defs = declare.modules(mods)"
  let #(defs, declare_errors) = declare.modules(mods)
  case list.length(declare_errors) {
    0 -> Nil
    n -> {
      list.map(declare_errors, fn(err) {
        io.println_error("❌ " <> error.display_syntax(err))
      })
      io.println_error(int.to_string(n) <> " declare errors")
    }
  }
  list.map(defs, fn(def) {
    let #(mod_name, mod_defs) = def
    io.println(string.inspect(mod_name) <> ":")
    list.map(mod_defs, fn(local) {
      let #(name, stmt) = local
      let stmt_str = case stmt.data {
        tao.Import(path, _alias, _scope) -> "import " <> path
        tao.Extern(_name, _params, _returns) -> "extern"
        tao.LetVar(_name, _opt_type, _value) -> "let-var"
        tao.LetPat(pattern, _types, _value) ->
          "let-pat " <> string.inspect(pattern)
        tao.LetMut(_name, _opt_type, _value) -> "let-mut"
        tao.Mut(_name, _value) -> todo
        tao.Test(_name, _expr, _expect) -> "test"
        tao.FnDef(_name, _implicits, _params, _returns, _body) -> "fn"
        tao.FnOverload(_name, _choices) -> "fn-overload"
        tao.TypeDef(_, _) -> "type"
        tao.For(_iterator, _range, _body) -> todo
        tao.While(_condition, _body) -> todo
        tao.Return(_expr) -> todo
        tao.Break -> todo
        tao.Continue -> todo
      }
      io.println("  - " <> string.inspect(name) <> ": " <> stmt_str)
    })
  })
  io.println("")

  echo "> ctx = define.types(ctx, defs, mods)"
  let ctx = define.types(ctx, defs)
  // list.map(list.zip(ctx.types, ctx.env), fn(entry) {
  //   let #(#(name, mod_type), mod_value) = entry
  //   io.print("ctx.env[" <> string.inspect(name) <> "]: ")
  //   io.println(fmt_value(mod_value))
  //   io.print("ctx.types[" <> string.inspect(name) <> "]: ")
  //   io.println(fmt_value(mod_type))
  //   io.println("")
  // })

  echo "> ctx = define.values(ctx, defs)"
  let ctx = define.values(ctx, defs)
  // list.map(list.zip(ctx.types, ctx.env), fn(entry) {
  //   let #(#(name, mod_type), mod_value) = entry
  //   io.print("ctx.env[" <> string.inspect(name) <> "]: ")
  //   io.println(fmt_value(mod_value))
  //   // io.print("ctx.types[" <> string.inspect(name) <> "]: ")
  //   // io.println(fmt_value(mod_type))
  //   io.println("")
  // })

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
  //   let #(id, #(_, value)) = entry
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

  echo "> test_defs, ctx = compile.tests(ctx, [mod])"
  let #(test_defs, ctx) = compile.tests(ctx, [mod])
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
